import CommitGolfCandidate.HybWrapHash

/-! One level of a record's expansion (16 donor words at word `D`). The 5-ary levels copy the four
rotation slots from the buffer; the binary levels clear the block and copy the sibling to block
words `12 b … 12 b + 3` (`b` the record node's parity), from the buffer (levels 2-15) or from the
scratch tables (levels 16-21). Along the way `x22` walks the node index, `x23` accumulates the
virtual index and `x1` the power of five. -/

namespace TwoPermutationPrototype.HybWrap
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Checker TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.CheckActions
open TwoPermutationPrototype.Quad.Checker (packedImage)

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/-- Word of the record buffer. -/
def BUFW : Nat := 33685504

def levelOff (k : Nat) : Nat := if k < 2 then 769 + 38*k else if k < 16 then 845 + 33*(k-2) else 1307 + 39*(k-16)

theorem level_codes : ∀ k < 22, WrapAt (levelOff k) (levelCode k) := by decide

/-- Registers at the start of level `k` (block at word `D`, node `n`, partial virtual index `V`). -/
structure LevelPre (k D n V : Nat) (s : MachineState) : Prop where
  x7 : s.getReg .x7 = BitVec.ofNat 64 (8*D)
  x20 : s.getReg .x20 = BitVec.ofNat 64 BUF
  x22 : s.getReg .x22 = BitVec.ofNat 64 n
  x23 : s.getReg .x23 = BitVec.ofNat 64 V
  x1 : s.getReg .x1 = BitVec.ofNat 64 (5^k)
  x4 : s.getReg .x4 = BitVec.ofNat 64 5
  x30 : s.getReg .x30 = BitVec.ofNat 64 96
  x5 : s.getReg .x5 = BitVec.ofNat 64 368

/-- Registers a level leaves alone. -/
def LevelKept (r : Reg) : Prop :=
  r ≠ .x1 ∧ r ≠ .x3 ∧ r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x22 ∧ r ≠ .x23 ∧ r ≠ .x31

/-! ### 5-ary levels -/

def pentaActs (k D n V : Nat) : List Action :=
  [.alu (.REMU .x3 .x22 .x4) .x3 (BitVec.ofNat 64 (n%5)), .alu (.DIVU .x22 .x22 .x4) .x22 (BitVec.ofNat 64 (n/5)),
   .alu (.MUL .x12 .x3 .x1) .x12 (BitVec.ofNat 64 (n%5*5^k)),
   .alu (.ADD .x23 .x23 .x12) .x23 (BitVec.ofNat 64 (V+n%5*5^k)),
   .alu (.MUL .x1 .x1 .x4) .x1 (BitVec.ofNat 64 (5^k*5))] ++
  copyActs .x20 .x7 (16+128*k) 0 (BUFW+2+16*k) D 16 ++ [.offset .x7 .x7 128 (BitVec.ofNat 64 (8*D+128))]

theorem penta_acts_op (k D n V : Nat) : (pentaActs k D n V).map Action.op = pentaLevel k := by
  simp only [pentaActs, List.map_append, copy_acts_op]; rfl

theorem penta_free (k D n V : Nat) : PermFree (pentaActs k D n V) := by
  refine perm_free_append (perm_free_append ?_ (copy_free _ _ _ _ _ _ _)) ?_
  · intro x hx; simp at hx; rcases hx with h | h | h | h | h <;> subst h <;> rfl
  · intro x hx; simp at hx; subst hx; rfl

theorem view_puts (s : MachineState) (r₁ r₂ : Reg) (v₁ v₂ : Word) :
    memoryView (putReg (putReg s r₁ v₁) r₂ v₂) = memoryView s := by rw [put_reg_view, put_reg_view]

theorem penta_level (o : Oracle) (k D n V : Nat) (s : MachineState) (hk : k < 2) (pre : LevelPre k D n V s)
    (hn : n < 2^40) (hV : V < 5^k) (hD : D + 16 ≤ 2^33) (far : BUFW + 2 + 16*k + 16 ≤ D) :
    validFixed o (pentaActs k D n V) s ∧ LevelPre (k+1) (D+16) (n/5) (V+n%5*5^k) (fixedOps o (pentaActs k D n V) s) ∧
      (∀ r, LevelKept r → (fixedOps o (pentaActs k D n V) s).getReg r = s.getReg r) ∧
      (∀ w < 2^33, memoryView (fixedOps o (pentaActs k D n V) s) w =
        if D ≤ w ∧ w < D+16 then memoryView s (BUFW+2+16*k+(w-D)) else memoryView s w) := by
  have p5 : 5^k ≤ 25 := by interval_cases k <;> decide
  have m5 : n%5 < 5 := Nat.mod_lt _ (by decide)
  let h₅ := putReg (putReg (putReg (putReg (putReg s .x3 (BitVec.ofNat 64 (n%5))) .x22 (BitVec.ofNat 64 (n/5)))
    .x12 (BitVec.ofNat 64 (n%5*5^k))) .x23 (BitVec.ofNat 64 (V+n%5*5^k))) .x1 (BitVec.ofNat 64 (5^k*5))
  have keep₅ : ∀ r, r ≠ .x3 → r ≠ .x22 → r ≠ .x12 → r ≠ .x23 → r ≠ .x1 → h₅.getReg r = s.getReg r := by
    intro r a b c d e
    simp only [h₅]
    rw [put_reg_reg, if_neg (fun h => e h.1.symm), put_reg_reg, if_neg (fun h => d h.1.symm), put_reg_reg,
      if_neg (fun h => c h.1.symm), put_reg_reg, if_neg (fun h => b h.1.symm), put_reg_reg, if_neg (fun h => a h.1.symm)]
  have bound12 : n%5*5^k ≤ 4*25 := Nat.mul_le_mul (by omega) p5
  have head : validFixed o ([.alu (.REMU .x3 .x22 .x4) .x3 (BitVec.ofNat 64 (n%5)),
      .alu (.DIVU .x22 .x22 .x4) .x22 (BitVec.ofNat 64 (n/5)), .alu (.MUL .x12 .x3 .x1) .x12 (BitVec.ofNat 64 (n%5*5^k)),
      .alu (.ADD .x23 .x23 .x12) .x23 (BitVec.ofNat 64 (V+n%5*5^k)),
      .alu (.MUL .x1 .x1 .x4) .x1 (BitVec.ofNat 64 (5^k*5))] : List Action) s := by
    refine ⟨?_, ?_, ?_, ?_, ?_, trivial⟩
    · apply alu_remu; rw [pre.x22, pre.x4, word_remu _ _ (by omega) (by decide) (by decide)]
    · apply alu_divu
      simp only [fixedStep, put_reg_reg, ne_eq, reduceCtorEq, false_and, if_false]
      rw [pre.x22, pre.x4, word_divu _ _ (by omega) (by decide) (by decide)]
    · apply alu_mul
      simp only [fixedStep, put_reg_reg, ne_eq, reduceCtorEq, false_and, if_false, not_false_eq_true, and_self,
        if_true]
      rw [pre.x1, word_mul _ _ (by omega) (by omega)]
    · apply alu_add
      simp only [fixedStep, put_reg_reg, ne_eq, reduceCtorEq, false_and, if_false, not_false_eq_true, and_self,
        if_true]
      rw [pre.x23, word_add _ _ (by omega)]
    · apply alu_mul
      simp only [fixedStep, put_reg_reg, ne_eq, reduceCtorEq, false_and, if_false, not_false_eq_true, and_self,
        if_true]
      rw [pre.x1, pre.x4, word_mul _ _ (by omega) (by decide)]
  have h20 : h₅.getReg .x20 = BitVec.ofNat 64 BUF := by rw [keep₅ .x20 (by decide) (by decide) (by decide) (by decide) (by decide), pre.x20]
  have h7 : h₅.getReg .x7 = BitVec.ofNat 64 (8*D) := by rw [keep₅ .x7 (by decide) (by decide) (by decide) (by decide) (by decide), pre.x7]
  obtain ⟨okC, regsC, memC⟩ := copy_run o h₅ .x20 .x7 (by decide) (by decide) (16+128*k) 0 (BUFW+2+16*k) D 16
    BUF (8*D) h20 h7 (by unfold BUF BUFW; omega) (by omega) (by omega) (by decide) (by unfold BUFW at *; omega) hD
    (Or.inl far)
  have headEq : fixedOps o ([.alu (.REMU .x3 .x22 .x4) .x3 (BitVec.ofNat 64 (n%5)),
      .alu (.DIVU .x22 .x22 .x4) .x22 (BitVec.ofNat 64 (n/5)), .alu (.MUL .x12 .x3 .x1) .x12 (BitVec.ofNat 64 (n%5*5^k)),
      .alu (.ADD .x23 .x23 .x12) .x23 (BitVec.ofNat 64 (V+n%5*5^k)),
      .alu (.MUL .x1 .x1 .x4) .x1 (BitVec.ofNat 64 (5^k*5))] : List Action) s = h₅ := rfl
  have fin : fixedOps o (pentaActs k D n V) s =
      putReg (fixedOps o (copyActs .x20 .x7 (16+128*k) 0 (BUFW+2+16*k) D 16) h₅) .x7 (BitVec.ofNat 64 (8*D+128)) := by
    unfold pentaActs; rw [fixedOps_append, fixedOps_append, headEq]; rfl
  generalize hc : fixedOps o (copyActs .x20 .x7 (16+128*k) 0 (BUFW+2+16*k) D 16) h₅ = c at okC regsC memC fin
  have cr : ∀ r, r ≠ .x31 → c.getReg r = h₅.getReg r := regsC
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold pentaActs
    rw [validFixed_append, validFixed_append, fixedOps_append, headEq, hc]
    refine ⟨⟨head, okC⟩, ?_, trivial⟩
    show c.getReg .x7 + _ = _
    rw [cr .x7 (by decide), h7, show (128 : BitVec 12) = BitVec.ofNat 12 128 from rfl,
      add_small _ 128 (by decide) (by omega)]
  · rw [fin]
    have g1 : h₅.getReg .x1 = BitVec.ofNat 64 (5^k*5) := by simp only [h₅]; rw [put_reg_reg, if_pos ⟨rfl, by decide⟩]
    have g23 : h₅.getReg .x23 = BitVec.ofNat 64 (V+n%5*5^k) := by
      simp only [h₅]; rw [put_reg_reg, if_neg (by decide), put_reg_reg, if_pos ⟨rfl, by decide⟩]
    have g22 : h₅.getReg .x22 = BitVec.ofNat 64 (n/5) := by
      simp only [h₅]; rw [put_reg_reg, if_neg (by decide), put_reg_reg, if_neg (by decide), put_reg_reg,
        if_neg (by decide), put_reg_reg, if_pos ⟨rfl, by decide⟩]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [put_reg_reg]
    · rw [if_pos ⟨rfl, by decide⟩]; congr 1
    · rw [if_neg (by decide), cr _ (by decide), h20]
    · rw [if_neg (by decide), cr _ (by decide), g22]
    · rw [if_neg (by decide), cr _ (by decide), g23]
    · rw [if_neg (by decide), cr _ (by decide), g1, pow_succ]
    · rw [if_neg (by decide), cr _ (by decide), keep₅ _ (by decide) (by decide) (by decide) (by decide) (by decide), pre.x4]
    · rw [if_neg (by decide), cr _ (by decide), keep₅ _ (by decide) (by decide) (by decide) (by decide) (by decide), pre.x30]
    · rw [if_neg (by decide), cr _ (by decide), keep₅ _ (by decide) (by decide) (by decide) (by decide) (by decide), pre.x5]
  · intro r kept
    obtain ⟨a, b, c', d, e, f, g, h, i, j⟩ := kept
    rw [fin, put_reg_reg, if_neg (fun hh => d hh.1.symm), cr r j, keep₅ r b h g i a]
  · intro w hw
    rw [fin, put_reg_view, memC w hw]
    simp only [h₅, view_puts, put_reg_view]

/-! ### Binary levels -/

def binArith (k n V : Nat) : List Action :=
  [.alu (.ANDI .x3 .x22 1) .x3 (BitVec.ofNat 64 (n%2)), .alu (.SRLI .x22 .x22 1) .x22 (BitVec.ofNat 64 (n/2)),
   .offset .x12 .x3 3 (BitVec.ofNat 64 (n%2+3)), .alu (.MUL .x12 .x12 .x1) .x12 (BitVec.ofNat 64 ((n%2+3)*5^k)),
   .alu (.ADD .x23 .x23 .x12) .x23 (BitVec.ofNat 64 (V+(n%2+3)*5^k)),
   .alu (.MUL .x1 .x1 .x4) .x1 (BitVec.ofNat 64 (5^k*5))]

def binDest (D n : Nat) : List Action :=
  [.alu (.MUL .x6 .x3 .x30) .x6 (BitVec.ofNat 64 (n%2*96)), .alu (.ADD .x6 .x6 .x7) .x6 (BitVec.ofNat 64 (8*(D+12*(n%2))))]

def binHeadActs (k D n V : Nat) : List Action := binArith k n V ++ zeroActs .x7 D 16 ++ binDest D n

theorem bin_head_op (k D n V : Nat) : (binHeadActs k D n V).map Action.op = binHead := by
  simp only [binHeadActs, List.map_append, zero_acts_op]; rfl

theorem bin_head_free (k D n V : Nat) : PermFree (binHeadActs k D n V) := by
  refine perm_free_append (perm_free_append ?_ (zero_free _ _ _)) ?_
  · intro x hx; simp [binArith] at hx; rcases hx with h | h | h | h | h | h <;> subst h <;> rfl
  · intro x hx; simp [binDest] at hx; rcases hx with h | h <;> subst h <;> rfl

/-- Registers after the binary head. -/
structure BinPost (k D n V : Nat) (s t : MachineState) : Prop where
  x3 : t.getReg .x3 = BitVec.ofNat 64 (n%2)
  x22 : t.getReg .x22 = BitVec.ofNat 64 (n/2)
  x23 : t.getReg .x23 = BitVec.ofNat 64 (V+(n%2+3)*5^k)
  x1 : t.getReg .x1 = BitVec.ofNat 64 (5^(k+1))
  x6 : t.getReg .x6 = BitVec.ofNat 64 (8*(D+12*(n%2)))
  keep : ∀ r, r ≠ .x1 → r ≠ .x3 → r ≠ .x6 → r ≠ .x12 → r ≠ .x22 → r ≠ .x23 → t.getReg r = s.getReg r

theorem bin_head (o : Oracle) (k D n V : Nat) (s : MachineState) (hk : k ≤ 21) (pre : LevelPre k D n V s)
    (hn : n < 2^40) (hV : V < 5^k) (hD : D + 16 ≤ 2^33) :
    validFixed o (binHeadActs k D n V) s ∧ BinPost k D n V s (fixedOps o (binHeadActs k D n V) s) ∧
      (∀ w < 2^33, memoryView (fixedOps o (binHeadActs k D n V) s) w =
        if D ≤ w ∧ w < D+16 then 0 else memoryView s w) := by
  have p5 : 5^k ≤ 5^21 := Nat.pow_le_pow_right (by decide) hk
  have p20 : (5:Nat)^21 = 476837158203125 := by norm_num
  have m2 : n%2 < 2 := Nat.mod_lt _ (by decide)
  have bound12 : (n%2+3)*5^k ≤ 4*5^k := Nat.mul_le_mul_right _ (by omega)
  let h₆ := putReg (putReg (putReg (putReg (putReg (putReg s .x3 (BitVec.ofNat 64 (n%2))) .x22 (BitVec.ofNat 64 (n/2)))
    .x12 (BitVec.ofNat 64 (n%2+3))) .x12 (BitVec.ofNat 64 ((n%2+3)*5^k))) .x23 (BitVec.ofNat 64 (V+(n%2+3)*5^k)))
    .x1 (BitVec.ofNat 64 (5^k*5))
  have arithEq : fixedOps o (binArith k n V) s = h₆ := rfl
  have keep₆ : ∀ r, r ≠ .x3 → r ≠ .x22 → r ≠ .x12 → r ≠ .x23 → r ≠ .x1 → h₆.getReg r = s.getReg r := by
    intro r a b c d e
    simp only [h₆]
    rw [put_reg_reg, if_neg (fun h => e h.1.symm), put_reg_reg, if_neg (fun h => d h.1.symm), put_reg_reg,
      if_neg (fun h => c h.1.symm), put_reg_reg, if_neg (fun h => c h.1.symm), put_reg_reg, if_neg (fun h => b h.1.symm),
      put_reg_reg, if_neg (fun h => a h.1.symm)]
  have arith : validFixed o (binArith k n V) s := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
    · apply alu_andi
      rw [pre.x22, show (1 : BitVec 12) = BitVec.ofNat 12 1 from rfl, word_and_one n (by omega)]
    · apply alu_srli
      simp only [fixedStep, put_reg_reg, ne_eq, reduceCtorEq, false_and, if_false]
      rw [pre.x22, show (1 : BitVec 6).toNat = 1 from rfl, word_shr _ _ (by omega), pow_one]
    · show (putReg (putReg s .x3 _) .x22 _).getReg .x3 + _ = _
      rw [put_reg_reg, if_neg (by decide), put_reg_reg, if_pos ⟨rfl, by decide⟩,
        show (3 : BitVec 12) = BitVec.ofNat 12 3 from rfl, add_small _ 3 (by decide) (by omega)]
    · apply alu_mul
      simp only [fixedStep, put_reg_reg, ne_eq, reduceCtorEq, false_and, if_false, not_false_eq_true, and_self,
        if_true]
      rw [pre.x1, word_mul _ _ (by omega) (by omega)]
    · apply alu_add
      simp only [fixedStep, put_reg_reg, ne_eq, reduceCtorEq, false_and, if_false, not_false_eq_true, and_self,
        if_true]
      rw [pre.x23, word_add _ _ (by omega)]
    · apply alu_mul
      simp only [fixedStep, put_reg_reg, ne_eq, reduceCtorEq, false_and, if_false, not_false_eq_true, and_self,
        if_true]
      rw [pre.x1, pre.x4, word_mul _ _ (by omega) (by decide)]
  have h7 : h₆.getReg .x7 = BitVec.ofNat 64 (8*D) := by
    rw [keep₆ .x7 (by decide) (by decide) (by decide) (by decide) (by decide), pre.x7]
  obtain ⟨okZ, regsZ, memZ⟩ := zero_run o h₆ .x7 D 16 h7 (by decide) hD
  generalize hz : fixedOps o (zeroActs .x7 D 16) h₆ = z at okZ regsZ memZ
  have z3 : z.getReg .x3 = BitVec.ofNat 64 (n%2) := by
    rw [regsZ]; simp only [h₆]
    rw [put_reg_reg, if_neg (by decide), put_reg_reg, if_neg (by decide), put_reg_reg, if_neg (by decide),
      put_reg_reg, if_neg (by decide), put_reg_reg, if_neg (by decide), put_reg_reg, if_pos ⟨rfl, by decide⟩]
  have z30 : z.getReg .x30 = BitVec.ofNat 64 96 := by
    rw [regsZ, keep₆ .x30 (by decide) (by decide) (by decide) (by decide) (by decide), pre.x30]
  have z7 : z.getReg .x7 = BitVec.ofNat 64 (8*D) := by rw [regsZ, h7]
  have dest : validFixed o (binDest D n) z := by
    refine ⟨?_, ?_, trivial⟩
    · apply alu_mul; rw [z3, z30, word_mul _ _ (by omega) (by decide)]
    · apply alu_add
      simp only [fixedStep, put_reg_reg, ne_eq, reduceCtorEq, false_and, if_false, not_false_eq_true, and_self,
        if_true]
      rw [z7, word_add _ _ (by omega)]
      congr 1; omega
  have fin : fixedOps o (binHeadActs k D n V) s =
      putReg (putReg z .x6 (BitVec.ofNat 64 (n%2*96))) .x6 (BitVec.ofNat 64 (8*(D+12*(n%2)))) := by
    unfold binHeadActs; rw [fixedOps_append, fixedOps_append, arithEq, hz]; rfl
  refine ⟨?_, ?_, ?_⟩
  · unfold binHeadActs
    rw [validFixed_append, validFixed_append, fixedOps_append, arithEq, hz]
    exact ⟨⟨arith, okZ⟩, dest⟩
  · rw [fin]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [put_reg_reg, if_neg (by decide), put_reg_reg, if_neg (by decide), z3]
    · rw [put_reg_reg, if_neg (by decide), put_reg_reg, if_neg (by decide), regsZ]; simp only [h₆]
      rw [put_reg_reg, if_neg (by decide), put_reg_reg, if_neg (by decide), put_reg_reg, if_neg (by decide),
        put_reg_reg, if_neg (by decide), put_reg_reg, if_pos ⟨rfl, by decide⟩]
    · rw [put_reg_reg, if_neg (by decide), put_reg_reg, if_neg (by decide), regsZ]; simp only [h₆]
      rw [put_reg_reg, if_neg (by decide), put_reg_reg, if_pos ⟨rfl, by decide⟩]
    · rw [put_reg_reg, if_neg (by decide), put_reg_reg, if_neg (by decide), regsZ]; simp only [h₆]
      rw [put_reg_reg, if_pos ⟨rfl, by decide⟩, pow_succ]
    · rw [put_reg_reg, if_pos ⟨rfl, by decide⟩]
    · intro r a b c d e f
      rw [put_reg_reg, if_neg (fun h => c h.1.symm), put_reg_reg, if_neg (fun h => c h.1.symm), regsZ,
        keep₆ r b e d f a]
  · intro w hw
    rw [fin, view_puts, memZ w hw]
    simp only [h₆, put_reg_view]

def binLowActs (k D n V : Nat) : List Action :=
  binHeadActs k D n V ++ copyActs .x20 .x6 (272+32*(k-2)) 0 (BUFW+34+4*(k-2)) (D+12*(n%2)) 4 ++
    [.offset .x7 .x7 128 (BitVec.ofNat 64 (8*D+128))]

theorem bin_low_op (k D n V : Nat) : (binLowActs k D n V).map Action.op = binLow k := by
  simp only [binLowActs, List.map_append, bin_head_op, copy_acts_op]; rfl

theorem bin_low_free (k D n V : Nat) : PermFree (binLowActs k D n V) :=
  perm_free_append (perm_free_append (bin_head_free _ _ _ _) (copy_free _ _ _ _ _ _ _))
    (by intro x hx; simp at hx; subst hx; rfl)

/-- The tail shared by both binary variants: four sibling words copied from `x src` to `x6`, then `x7 += 128`. -/
theorem bin_tail (o : Oracle) (k D n V : Nat) (s h : MachineState) (src : Reg) (hs : src ≠ .x31) (hs6 : src ≠ .x6)
    (a S Sb : Nat) (h6 : h.getReg .x6 = BitVec.ofNat 64 (8*(D+12*(n%2)))) (srcv : h.getReg src = BitVec.ofNat 64 Sb)
    (sa : Sb + a = 8*S)
    (ra : a + 32 ≤ 2048) (bs : S + 4 ≤ 2^33) (hD : D + 16 ≤ 2^33) (disj : S + 4 ≤ D ∨ D + 16 ≤ S)
    (h7 : h.getReg .x7 = BitVec.ofNat 64 (8*D)) :
    let tail := copyActs src .x6 a 0 S (D+12*(n%2)) 4 ++ [.offset .x7 .x7 128 (BitVec.ofNat 64 (8*D+128))]
    validFixed o tail h ∧ (∀ r, r ≠ .x31 → r ≠ .x7 → (fixedOps o tail h).getReg r = h.getReg r) ∧
      (fixedOps o tail h).getReg .x7 = BitVec.ofNat 64 (8*(D+16)) ∧
      (∀ w < 2^33, memoryView (fixedOps o tail h) w =
        if D+12*(n%2) ≤ w ∧ w < D+12*(n%2)+4 then memoryView h (S+(w-(D+12*(n%2)))) else memoryView h w) := by
  intro tail
  have m2 : n%2 < 2 := Nat.mod_lt _ (by decide)
  obtain ⟨okC, regsC, memC⟩ := copy_run o h src .x6 hs (by decide) a 0 S (D+12*(n%2)) 4 Sb (8*(D+12*(n%2)))
    srcv h6 sa (by omega) ra (by decide) bs (by omega) (by omega)
  have fin : fixedOps o tail h =
      putReg (fixedOps o (copyActs src .x6 a 0 S (D+12*(n%2)) 4) h) .x7 (BitVec.ofNat 64 (8*D+128)) := by
    show fixedOps o (_ ++ _) h = _; rw [fixedOps_append]; rfl
  generalize hc : fixedOps o (copyActs src .x6 a 0 S (D+12*(n%2)) 4) h = c at okC regsC memC fin
  refine ⟨?_, ?_, ?_, ?_⟩
  · show validFixed o (_ ++ _) h
    rw [validFixed_append, hc]
    refine ⟨okC, ?_, trivial⟩
    show c.getReg .x7 + _ = _
    rw [regsC .x7 (by decide), h7, show (128 : BitVec 12) = BitVec.ofNat 12 128 from rfl,
      add_small _ 128 (by decide) (by omega)]
  · intro r a b
    rw [fin, put_reg_reg, if_neg (fun hh => b hh.1.symm), regsC r a]
  · rw [fin, put_reg_reg, if_pos ⟨rfl, by decide⟩]; congr 1
  · intro w hw; rw [fin, put_reg_view, memC w hw]

theorem bin_low (o : Oracle) (k D n V : Nat) (s : MachineState) (hk1 : 2 ≤ k) (hk : k ≤ 15) (pre : LevelPre k D n V s)
    (hn : n < 2^40) (hV : V < 5^k) (hD : D + 16 ≤ 2^33) (far : BUFW + 90 ≤ D) :
    validFixed o (binLowActs k D n V) s ∧
      LevelPre (k+1) (D+16) (n/2) (V+(n%2+3)*5^k) (fixedOps o (binLowActs k D n V) s) ∧
      (∀ r, LevelKept r → (fixedOps o (binLowActs k D n V) s).getReg r = s.getReg r) ∧
      (∀ w < 2^33, memoryView (fixedOps o (binLowActs k D n V) s) w =
        if D ≤ w ∧ w < D+16 then
          (if D+12*(n%2) ≤ w ∧ w < D+12*(n%2)+4 then memoryView s (BUFW+34+4*(k-2)+(w-(D+12*(n%2)))) else 0)
        else memoryView s w) := by
  obtain ⟨okH, post, memH⟩ := bin_head o k D n V s (by omega) pre hn hV hD
  generalize hh : fixedOps o (binHeadActs k D n V) s = h at okH post memH
  have h20 : h.getReg .x20 = BitVec.ofNat 64 BUF :=
    (post.keep .x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans pre.x20
  have h7 : h.getReg .x7 = BitVec.ofNat 64 (8*D) :=
    (post.keep .x7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans pre.x7
  obtain ⟨okT, regsT, x7T, memT⟩ := bin_tail o k D n V s h .x20 (by decide) (by decide) (272+32*(k-2))
    (BUFW+34+4*(k-2)) BUF post.x6 h20 (by unfold BUF BUFW; omega) (by omega) (by unfold BUFW; omega) hD
    (Or.inl (by omega)) h7
  have split : binLowActs k D n V = binHeadActs k D n V ++
      (copyActs .x20 .x6 (272+32*(k-2)) 0 (BUFW+34+4*(k-2)) (D+12*(n%2)) 4 ++
        [.offset .x7 .x7 128 (BitVec.ofNat 64 (8*D+128))]) := by
    unfold binLowActs; rw [List.append_assoc]
  rw [split, validFixed_append, fixedOps_append, hh]
  refine ⟨⟨okH, okT⟩, ?_, ?_, ?_⟩
  · refine ⟨x7T, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [regsT _ (by decide) (by decide), h20]
    · rw [regsT _ (by decide) (by decide), post.x22]
    · rw [regsT _ (by decide) (by decide), post.x23]
    · rw [regsT _ (by decide) (by decide), post.x1]
    · rw [regsT _ (by decide) (by decide), post.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), pre.x4]
    · rw [regsT _ (by decide) (by decide), post.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), pre.x30]
    · rw [regsT _ (by decide) (by decide), post.keep _ (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide), pre.x5]
  · intro r ⟨a, b, c, d, e, f, g, i, j, l⟩
    rw [regsT r l d, post.keep r a b c g i j]
  · intro w hw
    have m2 : n%2 < 2 := Nat.mod_lt _ (by decide)
    rw [memT w hw]
    by_cases blk : D+12*(n%2) ≤ w ∧ w < D+12*(n%2)+4
    · rw [if_pos blk, if_pos (by omega), if_pos blk, memH _ (by unfold BUFW at *; omega), if_neg (by omega)]
    · rw [if_neg blk, memH w hw]
      by_cases inside : D ≤ w ∧ w < D+16
      · rw [if_pos inside, if_pos inside, if_neg blk]
      · rw [if_neg inside, if_neg inside]

def srcActs (k n : Nat) : List Action :=
  [.alu (.MUL .x10 .x22 .x5) .x10 (BitVec.ofNat 64 (n/2*368)),
   .alu (.ADD .x10 .x10 .x11) .x10 (BitVec.ofNat 64 (n/2*368+(HB k+168))),
   .alu (.SLLI .x12 .x3 5) .x12 (BitVec.ofNat 64 (n%2*2^5)),
   .alu (.SUB .x10 .x10 .x12) .x10 (BitVec.ofNat 64 (8*slotW k (n+1-2*(n%2))))]

def binHighActs (k D n V : Nat) : List Action :=
  binHeadActs k D n V ++ liActs .x11 (HB k + 168) ++ srcActs k n ++
    (copyActs .x10 .x6 0 0 (slotW k (n+1-2*(n%2))) (D+12*(n%2)) 4 ++ [.offset .x7 .x7 128 (BitVec.ofNat 64 (8*D+128))])

theorem bin_high_op (k D n V : Nat) : (binHighActs k D n V).map Action.op = binHigh k := by
  simp only [binHighActs, binHigh, upSource, List.map_append, bin_head_op, copy_acts_op, li_acts_op,
    List.append_assoc]; rfl

theorem bin_high_free (k D n V : Nat) : PermFree (binHighActs k D n V) := by
  refine perm_free_append (perm_free_append (perm_free_append (bin_head_free _ _ _ _) (li_free _ _)) ?_)
    (perm_free_append (copy_free _ _ _ _ _ _ _) ?_)
  · intro x hx; simp [srcActs] at hx; rcases hx with h | h | h | h <;> subst h <;> rfl
  · intro x hx; simp at hx; subst hx; rfl

theorem high_li : ∀ k, 16 ≤ k → k ≤ 21 → LiOK (HB k + 168) := by
  intro k h1 h2; interval_cases k <;> decide

theorem bin_high (o : Oracle) (k D n V : Nat) (s : MachineState) (hk1 : 16 ≤ k) (hk : k ≤ 21) (pre : LevelPre k D n V s)
    (hn : n < pentaCount k) (hV : V < 5^k) (hD : D + 16 ≤ 2^33) (far : TEND ≤ D) :
    validFixed o (binHighActs k D n V) s ∧
      LevelPre (k+1) (D+16) (n/2) (V+(n%2+3)*5^k) (fixedOps o (binHighActs k D n V) s) ∧
      (∀ r, LevelKept r → (fixedOps o (binHighActs k D n V) s).getReg r = s.getReg r) ∧
      (∀ w < 2^33, memoryView (fixedOps o (binHighActs k D n V) s) w =
        if D ≤ w ∧ w < D+16 then
          (if D+12*(n%2) ≤ w ∧ w < D+12*(n%2)+4 then
            memoryView s (slotW k (n+1-2*(n%2))+(w-(D+12*(n%2)))) else 0)
        else memoryView s w) := by
  have hb := hb_val k (by omega) (by omega)
  have cnt := count_penta k (by omega) (by omega)
  have gk : n/2 < groups k := by unfold groups; omega
  have m2 : n%2 < 2 := Nat.mod_lt _ (by decide)
  have hn' : n < 2^40 := by
    have : pentaCount k ≤ 66 := by rw [← cnt]; interval_cases k <;> decide
    omega
  obtain ⟨okH, post, memH⟩ := bin_head o k D n V s (by omega) pre hn' hV hD
  generalize hh : fixedOps o (binHeadActs k D n V) s = h at okH post memH
  obtain ⟨okL, x11L, keepL, viewL⟩ := li_run o h .x11 (HB k + 168) (high_li k hk1 hk) (by decide)
  generalize hl : fixedOps o (liActs .x11 (HB k + 168)) h = l at okL x11L keepL viewL
  have l22 : l.getReg .x22 = BitVec.ofNat 64 (n/2) := (keepL .x22 (by decide)).trans post.x22
  have l3 : l.getReg .x3 = BitVec.ofNat 64 (n%2) := (keepL .x3 (by decide)).trans post.x3
  have l5 : l.getReg .x5 = BitVec.ofNat 64 368 := by
    rw [keepL .x5 (by decide), post.keep .x5 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), pre.x5]
  have slotB : 8*slotW k (n+1-2*(n%2)) + 32*(n%2) = n/2*368+(HB k+168) := by
    unfold slotW groupW
    rw [show (n+1-2*(n%2))/2 = n/2 by omega, show (n+1-2*(n%2))%2 = 1-n%2 by omega]
    omega
  have srcOK : validFixed o (srcActs k n) l := by
    refine ⟨?_, ?_, ?_, ?_, trivial⟩
    · apply alu_mul; rw [l22, l5, word_mul _ _ (by omega) (by decide)]
    · apply alu_add
      simp only [fixedStep, put_reg_reg, ne_eq, reduceCtorEq, false_and, if_false, not_false_eq_true, and_self,
        if_true]
      rw [x11L, word_add _ _ (by unfold TEND at *; omega)]
    · apply alu_slli
      simp only [fixedStep, put_reg_reg, ne_eq, reduceCtorEq, false_and, if_false]
      rw [l3, show (5 : BitVec 6).toNat = 5 from rfl, word_shl _ _ (by omega)]
    · apply alu_sub
      simp only [fixedStep, put_reg_reg, ne_eq, reduceCtorEq, false_and, if_false, not_false_eq_true, and_self,
        if_true]
      rw [word_sub _ _ (by omega) (by unfold TEND at *; omega)]
      congr 1; omega
  let x := putReg (putReg (putReg (putReg l .x10 (BitVec.ofNat 64 (n/2*368))) .x10
    (BitVec.ofNat 64 (n/2*368+(HB k+168)))) .x12 (BitVec.ofNat 64 (n%2*2^5))) .x10
    (BitVec.ofNat 64 (8*slotW k (n+1-2*(n%2))))
  have srcEq : fixedOps o (srcActs k n) l = x := rfl
  have xkeep : ∀ r, r ≠ .x10 → r ≠ .x12 → x.getReg r = l.getReg r := by
    intro r a b
    simp only [x]
    rw [put_reg_reg, if_neg (fun hh => a hh.1.symm), put_reg_reg, if_neg (fun hh => b hh.1.symm), put_reg_reg,
      if_neg (fun hh => a hh.1.symm), put_reg_reg, if_neg (fun hh => a hh.1.symm)]
  have x10 : x.getReg .x10 = BitVec.ofNat 64 (8*slotW k (n+1-2*(n%2))) := by
    simp only [x]; rw [put_reg_reg, if_pos ⟨rfl, by decide⟩]
  have xview : memoryView x = memoryView h := by
    simp only [x, put_reg_view]; exact viewL
  have x6 : x.getReg .x6 = BitVec.ofNat 64 (8*(D+12*(n%2))) := by
    rw [xkeep _ (by decide) (by decide), keepL _ (by decide), post.x6]
  have x7 : x.getReg .x7 = BitVec.ofNat 64 (8*D) := by
    rw [xkeep _ (by decide) (by decide), keepL _ (by decide),
      post.keep .x7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), pre.x7]
  have slotLt : slotW k (n+1-2*(n%2)) + 4 ≤ TEND := by
    unfold slotW groupW
    rw [show (n+1-2*(n%2))/2 = n/2 by omega, show (n+1-2*(n%2))%2 = 1-n%2 by omega]
    omega
  obtain ⟨okT, regsT, x7T, memT⟩ := bin_tail o k D n V s x .x10 (by decide) (by decide) 0
    (slotW k (n+1-2*(n%2))) (8*slotW k (n+1-2*(n%2))) x6 x10 (by omega) (by decide) (by unfold TEND at *; omega) hD
    (Or.inl (by omega)) x7
  have split : binHighActs k D n V = binHeadActs k D n V ++ liActs .x11 (HB k + 168) ++ srcActs k n ++
      (copyActs .x10 .x6 0 0 (slotW k (n+1-2*(n%2))) (D+12*(n%2)) 4 ++
        [.offset .x7 .x7 128 (BitVec.ofNat 64 (8*D+128))]) := rfl
  have whole : fixedOps o (binHighActs k D n V) s =
      fixedOps o (copyActs .x10 .x6 0 0 (slotW k (n+1-2*(n%2))) (D+12*(n%2)) 4 ++
        [.offset .x7 .x7 128 (BitVec.ofNat 64 (8*D+128))]) x := by
    rw [split, fixedOps_append o (binHeadActs k D n V ++ liActs .x11 (HB k + 168) ++ srcActs k n),
      fixedOps_append o (binHeadActs k D n V ++ liActs .x11 (HB k + 168)), fixedOps_append o (binHeadActs k D n V),
      hh, hl, srcEq]
  have chain : ∀ r, LevelKept r → x.getReg r = s.getReg r := by
    intro r ⟨a, b, c, d, e, f, g, i, j, l'⟩
    rw [xkeep r e g, keepL r f, post.keep r a b c g i j]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [split, validFixed_append o (binHeadActs k D n V ++ liActs .x11 (HB k + 168) ++ srcActs k n),
      validFixed_append o (binHeadActs k D n V ++ liActs .x11 (HB k + 168)), validFixed_append o (binHeadActs k D n V),
      fixedOps_append o (binHeadActs k D n V ++ liActs .x11 (HB k + 168)), fixedOps_append o (binHeadActs k D n V),
      hh, hl, srcEq]
    exact ⟨⟨⟨okH, okL⟩, srcOK⟩, okT⟩
  · rw [whole]
    refine ⟨x7T, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [regsT _ (by decide) (by decide), chain .x20 (by unfold LevelKept; decide), pre.x20]
    · rw [regsT _ (by decide) (by decide), xkeep _ (by decide) (by decide), l22]
    · rw [regsT _ (by decide) (by decide), xkeep _ (by decide) (by decide), keepL _ (by decide), post.x23]
    · rw [regsT _ (by decide) (by decide), xkeep _ (by decide) (by decide), keepL _ (by decide), post.x1]
    · rw [regsT _ (by decide) (by decide), chain .x4 (by unfold LevelKept; decide), pre.x4]
    · rw [regsT _ (by decide) (by decide), chain .x30 (by unfold LevelKept; decide), pre.x30]
    · rw [regsT _ (by decide) (by decide), chain .x5 (by unfold LevelKept; decide), pre.x5]
  · intro r kept
    rw [whole, regsT r kept.2.2.2.2.2.2.2.2.2 kept.2.2.2.1, chain r kept]
  · intro w hw
    rw [whole, memT w hw, xview]
    by_cases blk : D+12*(n%2) ≤ w ∧ w < D+12*(n%2)+4
    · rw [if_pos blk, if_pos (by omega), if_pos blk, memH _ (by unfold TEND at *; omega), if_neg (by omega)]
    · rw [if_neg blk, memH w hw]
      by_cases inside : D ≤ w ∧ w < D+16
      · rw [if_pos inside, if_pos inside, if_neg blk]
      · rw [if_neg inside, if_neg inside]

end TwoPermutationPrototype.HybWrap
