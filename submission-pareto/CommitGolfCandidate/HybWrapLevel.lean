import CommitGolfCandidate.HybWrapHash

/-! One level of a record's expansion (16 donor words at word `D`). The 5-ary levels 0-1 copy the four
rotation slots from the buffer; the 4-ary level 2 clears the block and copies the three compact
siblings to their donor slots; the binary levels 3-12 clear the block and copy the sibling from the
buffer to block words `12 b … 12 b + 3` (`b` the record node's parity); the 5-ary levels 13-16 copy
the four other slots of the record's group, in rotation order, from the scratch tables. Along the way `x22` walks the node index, `x23` accumulates the
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

def levelOff (k : Nat) : Nat :=
  if k < 5 then 1842 + 38*k else if k = 5 then 2032 else if k < 9 then 2100 + 33*(k-6) else 2199 + 58*(k-9)

theorem level_codes_0 : ∀ i < 4, WrapAt (levelOff (4*0+i)) (levelCode (4*0+i)) := by decide
theorem level_codes_1 : ∀ i < 4, WrapAt (levelOff (4*1+i)) (levelCode (4*1+i)) := by decide
theorem level_codes_2 : ∀ i < 4, WrapAt (levelOff (4*2+i)) (levelCode (4*2+i)) := by decide
theorem level_codes_3 : ∀ i < 1, WrapAt (levelOff (4*3+i)) (levelCode (4*3+i)) := by decide
theorem level_codes : ∀ g < 13, WrapAt (levelOff g) (levelCode g) := by
  intro g hg
  have e : g = 4*(g/4)+g%4 := by omega
  have hq : g/4 < 4 := by omega
  have hi : g%4 < 4 := Nat.mod_lt _ (by decide)
  have hr : g/4*4+g%4 < 13 := by omega
  rw [e]; revert hr hi hq; generalize g/4 = q; generalize g%4 = i; intro hq hi hr
  interval_cases q <;> first
    | exact level_codes_0 i (by omega)
    | exact level_codes_1 i (by omega)
    | exact level_codes_2 i (by omega)
    | exact level_codes_3 i (by omega)

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

theorem penta_level (o : Oracle) (k D n V : Nat) (s : MachineState) (hk : k < 5) (pre : LevelPre k D n V s)
    (hn : n < 2^40) (hV : V < 5^k) (hD : D + 16 ≤ 2^33) (far : BUFW + 2 + 16*k + 16 ≤ D) :
    validFixed o (pentaActs k D n V) s ∧ LevelPre (k+1) (D+16) (n/5) (V+n%5*5^k) (fixedOps o (pentaActs k D n V) s) ∧
      (∀ r, LevelKept r → (fixedOps o (pentaActs k D n V) s).getReg r = s.getReg r) ∧
      (∀ w < 2^33, memoryView (fixedOps o (pentaActs k D n V) s) w =
        if D ≤ w ∧ w < D+16 then memoryView s (BUFW+2+16*k+(w-D)) else memoryView s w) := by
  have p5 : 5^k ≤ 625 := by interval_cases k <;> decide
  have m5 : n%5 < 5 := Nat.mod_lt _ (by decide)
  let h₅ := putReg (putReg (putReg (putReg (putReg s .x3 (BitVec.ofNat 64 (n%5))) .x22 (BitVec.ofNat 64 (n/5)))
    .x12 (BitVec.ofNat 64 (n%5*5^k))) .x23 (BitVec.ofNat 64 (V+n%5*5^k))) .x1 (BitVec.ofNat 64 (5^k*5))
  have keep₅ : ∀ r, r ≠ .x3 → r ≠ .x22 → r ≠ .x12 → r ≠ .x23 → r ≠ .x1 → h₅.getReg r = s.getReg r := by
    intro r a b c d e
    simp only [h₅]
    rw [put_reg_reg, if_neg (fun h => e h.1.symm), put_reg_reg, if_neg (fun h => d h.1.symm), put_reg_reg,
      if_neg (fun h => c h.1.symm), put_reg_reg, if_neg (fun h => b h.1.symm), put_reg_reg, if_neg (fun h => a h.1.symm)]
  have bound12 : n%5*5^k ≤ 4*625 := Nat.mul_le_mul (by omega) p5
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
  binHeadActs k D n V ++ copyActs .x20 .x6 (752+32*(k-6)) 0 (BUFW+94+4*(k-6)) (D+12*(n%2)) 4 ++
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

theorem bin_low (o : Oracle) (k D n V : Nat) (s : MachineState) (hk1 : 6 ≤ k) (hk : k ≤ 8) (pre : LevelPre k D n V s)
    (hn : n < 2^40) (hV : V < 5^k) (hD : D + 16 ≤ 2^33) (far : BUFW + 106 ≤ D) :
    validFixed o (binLowActs k D n V) s ∧
      LevelPre (k+1) (D+16) (n/2) (V+(n%2+3)*5^k) (fixedOps o (binLowActs k D n V) s) ∧
      (∀ r, LevelKept r → (fixedOps o (binLowActs k D n V) s).getReg r = s.getReg r) ∧
      (∀ w < 2^33, memoryView (fixedOps o (binLowActs k D n V) s) w =
        if D ≤ w ∧ w < D+16 then
          (if D+12*(n%2) ≤ w ∧ w < D+12*(n%2)+4 then memoryView s (BUFW+94+4*(k-6)+(w-(D+12*(n%2)))) else 0)
        else memoryView s w) := by
  obtain ⟨okH, post, memH⟩ := bin_head o k D n V s (by omega) pre hn hV hD
  generalize hh : fixedOps o (binHeadActs k D n V) s = h at okH post memH
  have h20 : h.getReg .x20 = BitVec.ofNat 64 BUF :=
    (post.keep .x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans pre.x20
  have h7 : h.getReg .x7 = BitVec.ofNat 64 (8*D) :=
    (post.keep .x7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans pre.x7
  obtain ⟨okT, regsT, x7T, memT⟩ := bin_tail o k D n V s h .x20 (by decide) (by decide) (752+32*(k-6))
    (BUFW+94+4*(k-6)) BUF post.x6 h20 (by unfold BUF BUFW; omega) (by omega) (by unfold BUFW; omega) hD
    (Or.inl (by omega)) h7
  have split : binLowActs k D n V = binHeadActs k D n V ++
      (copyActs .x20 .x6 (752+32*(k-6)) 0 (BUFW+94+4*(k-6)) (D+12*(n%2)) 4 ++
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

/-! ### The 4-ary level 5 -/

def quadArith (n V : Nat) : List Action :=
  [.alu (.ANDI .x3 .x22 3) .x3 (BitVec.ofNat 64 (n%4)), .alu (.SRLI .x22 .x22 2) .x22 (BitVec.ofNat 64 (n/4)),
   .offset .x12 .x3 1 (BitVec.ofNat 64 (n%4+1)), .alu (.MUL .x12 .x12 .x1) .x12 (BitVec.ofNat 64 ((n%4+1)*3125)),
   .alu (.ADD .x23 .x23 .x12) .x23 (BitVec.ofNat 64 (V+(n%4+1)*3125)),
   .alu (.MUL .x1 .x1 .x4) .x1 (BitVec.ofNat 64 (3125*5))]

/-- Donor slot (0-3) of compact 4-ary sibling `t`. -/
def qslot (n t : Nat) : Nat := ((n%4+t+1)%4+4-n%4)%5

def quadSibActs (D n t : Nat) : List Action :=
  [.offset .x10 .x3 (BitVec.ofNat 12 (t+1)) (BitVec.ofNat 64 (n%4+t+1)),
   .alu (.ANDI .x10 .x10 3) .x10 (BitVec.ofNat 64 ((n%4+t+1)%4)),
   .offset .x10 .x10 4 (BitVec.ofNat 64 ((n%4+t+1)%4+4)),
   .alu (.SUB .x10 .x10 .x3) .x10 (BitVec.ofNat 64 ((n%4+t+1)%4+4-n%4)),
   .alu (.REMU .x10 .x10 .x4) .x10 (BitVec.ofNat 64 (qslot n t)),
   .alu (.SLLI .x10 .x10 5) .x10 (BitVec.ofNat 64 (qslot n t*2^5)),
   .alu (.ADD .x10 .x10 .x7) .x10 (BitVec.ofNat 64 (8*(D+4*qslot n t)))] ++
  copyActs .x20 .x10 (656+32*t) 0 (BUFW+82+4*t) (D+4*qslot n t) 4

def quadActs (D n V : Nat) : List Action :=
  quadArith n V ++ zeroActs .x7 D 16 ++ (quadSibActs D n 0 ++ (quadSibActs D n 1 ++ quadSibActs D n 2)) ++
    [.offset .x7 .x7 128 (BitVec.ofNat 64 (8*D+128))]

theorem quad_acts_op (D n V : Nat) : (quadActs D n V).map Action.op = quadLevel := by
  simp only [quadActs, quadSibActs, quadLevel, quadHead, quadSib, List.map_append, zero_acts_op, copy_acts_op,
    List.range_succ, List.range_zero, List.flatMap_append, List.flatMap_nil, List.flatMap_cons, List.nil_append,
    List.append_nil, List.append_assoc]
  rfl

theorem quad_free (D n V : Nat) : PermFree (quadActs D n V) := by
  have sib : ∀ t, PermFree (quadSibActs D n t) := by
    intro t
    refine perm_free_append ?_ (copy_free _ _ _ _ _ _ _)
    intro x hx; simp at hx; rcases hx with h | h | h | h | h | h | h <;> subst h <;> rfl
  refine perm_free_append (perm_free_append (perm_free_append ?_ (zero_free _ _ _))
    (perm_free_append (sib 0) (perm_free_append (sib 1) (sib 2)))) ?_
  · intro x hx; simp [quadArith] at hx; rcases hx with h | h | h | h | h | h <;> subst h <;> rfl
  · intro x hx; simp at hx; subst hx; rfl

theorem word_and_three (a : Nat) (ha : a < 2^64) :
    BitVec.ofNat 64 a &&& signExtend12 (BitVec.ofNat 12 3) = BitVec.ofNat 64 (a%4) := by
  rw [sext_small 3 (by decide)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    show 3 % 2^64 = 3 from rfl, show (3 : Nat) = 2^2-1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    show (2:Nat)^2 = 4 from rfl, Nat.mod_eq_of_lt (by omega : a % 4 < 2^64)]

theorem qslot_lt (n t : Nat) : qslot n t < 5 := Nat.mod_lt _ (by decide)

theorem qslot_lt4 (n t : Nat) (ht : t < 3) : qslot n t < 4 := by
  unfold qslot
  have h := Nat.mod_lt n (show 4 > 0 by decide)
  generalize n % 4 = d at h ⊢
  interval_cases d <;> interval_cases t <;> decide

/-- One compact 4-ary sibling copy (registers `x3 = n % 4`, `x4 = 5`, `x7 = 8 D`, `x20 = BUF`). -/
theorem quad_sib (o : Oracle) (D n t : Nat) (s : MachineState) (ht : t < 3) (hD : D + 16 ≤ 2^33)
    (far : BUFW + 106 ≤ D)
    (x3 : s.getReg .x3 = BitVec.ofNat 64 (n%4)) (x4 : s.getReg .x4 = BitVec.ofNat 64 5)
    (x7 : s.getReg .x7 = BitVec.ofNat 64 (8*D)) (x20 : s.getReg .x20 = BitVec.ofNat 64 BUF) :
    validFixed o (quadSibActs D n t) s ∧
      (∀ r, r ≠ .x10 → r ≠ .x31 → (fixedOps o (quadSibActs D n t) s).getReg r = s.getReg r) ∧
      (∀ w < 2^33, memoryView (fixedOps o (quadSibActs D n t) s) w =
        if D+4*qslot n t ≤ w ∧ w < D+4*qslot n t+4 then memoryView s (BUFW+82+4*t+(w-(D+4*qslot n t)))
        else memoryView s w) := by
  have m4 : n%4 < 4 := Nat.mod_lt _ (by decide)
  have e4 : (n%4+t+1)%4 < 4 := Nat.mod_lt _ (by decide)
  have q5 := qslot_lt4 n t ht
  let a := putReg (putReg (putReg (putReg (putReg (putReg (putReg s .x10 (BitVec.ofNat 64 (n%4+t+1))) .x10
    (BitVec.ofNat 64 ((n%4+t+1)%4))) .x10 (BitVec.ofNat 64 ((n%4+t+1)%4+4))) .x10
    (BitVec.ofNat 64 ((n%4+t+1)%4+4-n%4))) .x10 (BitVec.ofNat 64 (qslot n t))) .x10
    (BitVec.ofNat 64 (qslot n t*2^5))) .x10 (BitVec.ofNat 64 (8*(D+4*qslot n t)))
  have arithEq : fixedOps o ([.offset .x10 .x3 (BitVec.ofNat 12 (t+1)) (BitVec.ofNat 64 (n%4+t+1)),
      .alu (.ANDI .x10 .x10 3) .x10 (BitVec.ofNat 64 ((n%4+t+1)%4)),
      .offset .x10 .x10 4 (BitVec.ofNat 64 ((n%4+t+1)%4+4)),
      .alu (.SUB .x10 .x10 .x3) .x10 (BitVec.ofNat 64 ((n%4+t+1)%4+4-n%4)),
      .alu (.REMU .x10 .x10 .x4) .x10 (BitVec.ofNat 64 (qslot n t)),
      .alu (.SLLI .x10 .x10 5) .x10 (BitVec.ofNat 64 (qslot n t*2^5)),
      .alu (.ADD .x10 .x10 .x7) .x10 (BitVec.ofNat 64 (8*(D+4*qslot n t)))] : List Action) s = a := rfl
  have akeep : ∀ r, r ≠ .x10 → a.getReg r = s.getReg r := by
    intro r h
    simp only [a]
    rw [put_reg_reg, if_neg (fun hh => h hh.1.symm), put_reg_reg, if_neg (fun hh => h hh.1.symm), put_reg_reg,
      if_neg (fun hh => h hh.1.symm), put_reg_reg, if_neg (fun hh => h hh.1.symm), put_reg_reg,
      if_neg (fun hh => h hh.1.symm), put_reg_reg, if_neg (fun hh => h hh.1.symm), put_reg_reg,
      if_neg (fun hh => h hh.1.symm)]
  have a10 : a.getReg .x10 = BitVec.ofNat 64 (8*(D+4*qslot n t)) := by
    simp only [a]; rw [put_reg_reg, if_pos ⟨rfl, by decide⟩]
  have arith : validFixed o ([.offset .x10 .x3 (BitVec.ofNat 12 (t+1)) (BitVec.ofNat 64 (n%4+t+1)),
      .alu (.ANDI .x10 .x10 3) .x10 (BitVec.ofNat 64 ((n%4+t+1)%4)),
      .offset .x10 .x10 4 (BitVec.ofNat 64 ((n%4+t+1)%4+4)),
      .alu (.SUB .x10 .x10 .x3) .x10 (BitVec.ofNat 64 ((n%4+t+1)%4+4-n%4)),
      .alu (.REMU .x10 .x10 .x4) .x10 (BitVec.ofNat 64 (qslot n t)),
      .alu (.SLLI .x10 .x10 5) .x10 (BitVec.ofNat 64 (qslot n t*2^5)),
      .alu (.ADD .x10 .x10 .x7) .x10 (BitVec.ofNat 64 (8*(D+4*qslot n t)))] : List Action) s := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
    · show s.getReg .x3 + signExtend12 (BitVec.ofNat 12 (t+1)) = _
      rw [x3, add_small _ _ (by omega) (by omega)]; congr 1
    · apply alu_andi
      simp only [fixedStep, put_reg_reg, ne_eq, reduceCtorEq, false_and, if_false, not_false_eq_true, and_self,
        if_true]
      rw [show (3 : BitVec 12) = BitVec.ofNat 12 3 from rfl, word_and_three _ (by omega)]
    · show (putReg (putReg s .x10 _) .x10 _).getReg .x10 + _ = _
      rw [put_reg_reg, if_pos ⟨rfl, by decide⟩, show (4 : BitVec 12) = BitVec.ofNat 12 4 from rfl,
        add_small _ 4 (by decide) (by omega)]
    · apply alu_sub
      simp only [fixedStep, put_reg_reg, ne_eq, reduceCtorEq, false_and, if_false, not_false_eq_true, and_self,
        if_true]
      rw [x3, word_sub _ _ (by omega) (by omega)]
    · apply alu_remu
      simp only [fixedStep, put_reg_reg, ne_eq, reduceCtorEq, false_and, if_false, not_false_eq_true, and_self,
        if_true]
      rw [x4, word_remu _ _ (by omega) (by decide) (by decide)]; rfl
    · apply alu_slli
      simp only [fixedStep, put_reg_reg, ne_eq, reduceCtorEq, false_and, if_false, not_false_eq_true, and_self,
        if_true]
      rw [show (5 : BitVec 6).toNat = 5 from rfl, word_shl _ _ (by omega)]
    · apply alu_add
      simp only [fixedStep, put_reg_reg, ne_eq, reduceCtorEq, false_and, if_false, not_false_eq_true, and_self,
        if_true]
      rw [x7, word_add _ _ (by omega)]
      congr 1; omega
  have a20 : a.getReg .x20 = BitVec.ofNat 64 BUF := (akeep .x20 (by decide)).trans x20
  obtain ⟨okC, regsC, memC⟩ := copy_run o a .x20 .x10 (by decide) (by decide) (656+32*t) 0 (BUFW+82+4*t)
    (D+4*qslot n t) 4 BUF (8*(D+4*qslot n t)) a20 a10 (by unfold BUF BUFW; omega) (by omega) (by omega) (by decide)
    (by unfold BUFW; omega) (by omega) (Or.inl (by unfold BUFW at *; omega))
  have fin : fixedOps o (quadSibActs D n t) s =
      fixedOps o (copyActs .x20 .x10 (656+32*t) 0 (BUFW+82+4*t) (D+4*qslot n t) 4) a := by
    unfold quadSibActs; rw [fixedOps_append, arithEq]
  have aview : memoryView a = memoryView s := by simp only [a, put_reg_view]
  refine ⟨?_, ?_, ?_⟩
  · unfold quadSibActs; rw [validFixed_append, arithEq]; exact ⟨arith, okC⟩
  · intro r h10 h31; rw [fin, regsC r h31, akeep r h10]
  · intro w hw; rw [fin, memC w hw, aview]

/-- Which compact sibling lands in donor slot `j`, or none (slot 0 of the group). -/
theorem qslot_cases (d j : Nat) (hd : d < 4) (hj : j < 4) :
    ((d+j+2)%5 = 0 ∧ ∀ t < 3, ((d+t+1)%4+4-d)%5 ≠ j) ∨
    ((d+j+2)%5 ≠ 0 ∧ ((d+((d+j+2)%5+6-d)%4+1)%4+4-d)%5 = j ∧ ((d+j+2)%5+6-d)%4 < 3 ∧
      ∀ t < 3, t ≠ ((d+j+2)%5+6-d)%4 → ((d+t+1)%4+4-d)%5 ≠ j) := by
  interval_cases d <;> interval_cases j <;> decide

theorem quad_level (o : Oracle) (D n V : Nat) (s : MachineState) (pre : LevelPre 5 D n V s)
    (hn : n < 2^40) (hV : V < 3125) (hD : D + 16 ≤ 2^33) (far : BUFW + 106 ≤ D) :
    validFixed o (quadActs D n V) s ∧
      LevelPre 6 (D+16) (n/4) (V+(n%4+1)*3125) (fixedOps o (quadActs D n V) s) ∧
      (∀ r, LevelKept r → (fixedOps o (quadActs D n V) s).getReg r = s.getReg r) ∧
      (∀ w < 2^33, memoryView (fixedOps o (quadActs D n V) s) w =
        if D ≤ w ∧ w < D+16 then
          (if (n%4+(w-D)/4+2)%5 = 0 then 0
           else memoryView s (BUFW+82+4*(((n%4+(w-D)/4+2)%5+6-n%4)%4)+(w-D)%4))
        else memoryView s w) := by
  have m4 : n%4 < 4 := Nat.mod_lt _ (by decide)
  have x1v : s.getReg .x1 = BitVec.ofNat 64 3125 := pre.x1
  let h₆ := putReg (putReg (putReg (putReg (putReg (putReg s .x3 (BitVec.ofNat 64 (n%4))) .x22 (BitVec.ofNat 64 (n/4)))
    .x12 (BitVec.ofNat 64 (n%4+1))) .x12 (BitVec.ofNat 64 ((n%4+1)*3125))) .x23 (BitVec.ofNat 64 (V+(n%4+1)*3125)))
    .x1 (BitVec.ofNat 64 (3125*5))
  have arithEq : fixedOps o (quadArith n V) s = h₆ := rfl
  have keep₆ : ∀ r, r ≠ .x3 → r ≠ .x22 → r ≠ .x12 → r ≠ .x23 → r ≠ .x1 → h₆.getReg r = s.getReg r := by
    intro r a b c d e
    simp only [h₆]
    rw [put_reg_reg, if_neg (fun h => e h.1.symm), put_reg_reg, if_neg (fun h => d h.1.symm), put_reg_reg,
      if_neg (fun h => c h.1.symm), put_reg_reg, if_neg (fun h => c h.1.symm), put_reg_reg, if_neg (fun h => b h.1.symm),
      put_reg_reg, if_neg (fun h => a h.1.symm)]
  have arith : validFixed o (quadArith n V) s := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
    · apply alu_andi
      rw [pre.x22, show (3 : BitVec 12) = BitVec.ofNat 12 3 from rfl, word_and_three n (by omega)]
    · apply alu_srli
      simp only [fixedStep, put_reg_reg, ne_eq, reduceCtorEq, false_and, if_false]
      rw [pre.x22, show (2 : BitVec 6).toNat = 2 from rfl, word_shr _ _ (by omega)]; rfl
    · show (putReg (putReg s .x3 _) .x22 _).getReg .x3 + _ = _
      rw [put_reg_reg, if_neg (by decide), put_reg_reg, if_pos ⟨rfl, by decide⟩,
        show (1 : BitVec 12) = BitVec.ofNat 12 1 from rfl, add_small _ 1 (by decide) (by omega)]
    · apply alu_mul
      simp only [fixedStep, put_reg_reg, ne_eq, reduceCtorEq, false_and, if_false, not_false_eq_true, and_self,
        if_true]
      rw [x1v, word_mul _ _ (by omega) (by decide)]
    · apply alu_add
      simp only [fixedStep, put_reg_reg, ne_eq, reduceCtorEq, false_and, if_false, not_false_eq_true, and_self,
        if_true]
      rw [pre.x23, word_add _ _ (by omega)]
    · apply alu_mul
      simp only [fixedStep, put_reg_reg, ne_eq, reduceCtorEq, false_and, if_false, not_false_eq_true, and_self,
        if_true]
      rw [x1v, pre.x4, word_mul _ _ (by decide) (by decide)]
  have h7 : h₆.getReg .x7 = BitVec.ofNat 64 (8*D) := by
    rw [keep₆ .x7 (by decide) (by decide) (by decide) (by decide) (by decide), pre.x7]
  obtain ⟨okZ, regsZ, memZ⟩ := zero_run o h₆ .x7 D 16 h7 (by decide) hD
  generalize hz : fixedOps o (zeroActs .x7 D 16) h₆ = z at okZ regsZ memZ
  have z3 : z.getReg .x3 = BitVec.ofNat 64 (n%4) := by
    rw [regsZ]; simp only [h₆]
    rw [put_reg_reg, if_neg (by decide), put_reg_reg, if_neg (by decide), put_reg_reg, if_neg (by decide),
      put_reg_reg, if_neg (by decide), put_reg_reg, if_neg (by decide), put_reg_reg, if_pos ⟨rfl, by decide⟩]
  have zk : ∀ r, r ≠ .x3 → r ≠ .x22 → r ≠ .x12 → r ≠ .x23 → r ≠ .x1 → z.getReg r = s.getReg r := by
    intro r a b c d e; rw [regsZ, keep₆ r a b c d e]
  have z4 : z.getReg .x4 = BitVec.ofNat 64 5 := (zk .x4 (by decide) (by decide) (by decide) (by decide) (by decide)).trans pre.x4
  have z7 : z.getReg .x7 = BitVec.ofNat 64 (8*D) := by rw [regsZ, h7]
  have z20 : z.getReg .x20 = BitVec.ofNat 64 BUF := (zk .x20 (by decide) (by decide) (by decide) (by decide) (by decide)).trans pre.x20
  -- the three sibling copies
  obtain ⟨ok0, regs0, mem0⟩ := quad_sib o D n 0 z (by decide) hD far z3 z4 z7 z20
  generalize h0 : fixedOps o (quadSibActs D n 0) z = c0 at ok0 regs0 mem0
  obtain ⟨ok1, regs1, mem1⟩ := quad_sib o D n 1 c0 (by decide) hD far
    ((regs0 .x3 (by decide) (by decide)).trans z3) ((regs0 .x4 (by decide) (by decide)).trans z4)
    ((regs0 .x7 (by decide) (by decide)).trans z7) ((regs0 .x20 (by decide) (by decide)).trans z20)
  generalize h1 : fixedOps o (quadSibActs D n 1) c0 = c1 at ok1 regs1 mem1
  obtain ⟨ok2, regs2, mem2⟩ := quad_sib o D n 2 c1 (by decide) hD far
    ((regs1 .x3 (by decide) (by decide)).trans ((regs0 .x3 (by decide) (by decide)).trans z3))
    ((regs1 .x4 (by decide) (by decide)).trans ((regs0 .x4 (by decide) (by decide)).trans z4))
    ((regs1 .x7 (by decide) (by decide)).trans ((regs0 .x7 (by decide) (by decide)).trans z7))
    ((regs1 .x20 (by decide) (by decide)).trans ((regs0 .x20 (by decide) (by decide)).trans z20))
  generalize h2 : fixedOps o (quadSibActs D n 2) c1 = c2 at ok2 regs2 mem2
  have r21 : ∀ r, r ≠ .x10 → r ≠ .x31 → c2.getReg r = z.getReg r := fun r a b => by
    rw [regs2 r a b, regs1 r a b, regs0 r a b]
  have c7 : c2.getReg .x7 = BitVec.ofNat 64 (8*D) := (r21 .x7 (by decide) (by decide)).trans z7
  have fin : fixedOps o (quadActs D n V) s = putReg c2 .x7 (BitVec.ofNat 64 (8*D+128)) := by
    unfold quadActs
    simp only [fixedOps_append]
    rw [arithEq, hz, h0, h1, h2]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold quadActs
    simp only [validFixed_append, fixedOps_append]
    rw [arithEq, hz, h0, h1, h2]
    refine ⟨⟨⟨arith, okZ⟩, ok0, ok1, ok2⟩, ?_, trivial⟩
    show c2.getReg .x7 + _ = _
    rw [c7, show (128 : BitVec 12) = BitVec.ofNat 12 128 from rfl, add_small _ 128 (by decide) (by omega)]
  · rw [fin]
    have zr : ∀ r, r ≠ .x10 → r ≠ .x31 → r ≠ .x7 → (putReg c2 .x7 (BitVec.ofNat 64 (8*D+128))).getReg r = z.getReg r :=
      fun r a b c => by rw [put_reg_reg, if_neg (fun hh => c hh.1.symm), r21 r a b]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [put_reg_reg, if_pos ⟨rfl, by decide⟩]; congr 1
    · rw [zr _ (by decide) (by decide) (by decide), z20]
    · rw [zr _ (by decide) (by decide) (by decide), regsZ]; simp only [h₆]
      rw [put_reg_reg, if_neg (by decide), put_reg_reg, if_neg (by decide), put_reg_reg, if_neg (by decide),
        put_reg_reg, if_neg (by decide), put_reg_reg, if_pos ⟨rfl, by decide⟩]
    · rw [zr _ (by decide) (by decide) (by decide), regsZ]; simp only [h₆]
      rw [put_reg_reg, if_neg (by decide), put_reg_reg, if_pos ⟨rfl, by decide⟩]
    · rw [zr _ (by decide) (by decide) (by decide), regsZ]; simp only [h₆]
      rw [put_reg_reg, if_pos ⟨rfl, by decide⟩]; rfl
    · rw [zr _ (by decide) (by decide) (by decide), z4]
    · rw [zr _ (by decide) (by decide) (by decide), zk _ (by decide) (by decide) (by decide) (by decide) (by decide), pre.x30]
    · rw [zr _ (by decide) (by decide) (by decide), zk _ (by decide) (by decide) (by decide) (by decide) (by decide), pre.x5]
  · intro r ⟨a, b, c, d, e, f, g, i, j, l⟩
    rw [fin, put_reg_reg, if_neg (fun hh => d hh.1.symm), r21 r e l, zk r b i g j a]
  · intro w hw
    rw [fin, put_reg_view, mem2 w hw]
    have q0 := qslot_lt4 n 0 (by decide)
    have q1 := qslot_lt4 n 1 (by decide)
    have q2 := qslot_lt4 n 2 (by decide)
    have qlt : ∀ t < 3, qslot n t < 4 := fun t ht => qslot_lt4 n t ht
    have bufz : ∀ t < 3, ∀ q < 4, memoryView z (BUFW+82+4*t+q) = memoryView s (BUFW+82+4*t+q) := by
      intro t ht q hq
      rw [memZ _ (by unfold BUFW; omega), if_neg (by unfold BUFW at *; omega)]; simp only [h₆, put_reg_view]
    have buf1 : ∀ t < 3, ∀ q < 4, memoryView c0 (BUFW+82+4*t+q) = memoryView z (BUFW+82+4*t+q) := by
      intro t ht q hq; rw [mem0 _ (by unfold BUFW; omega), if_neg (by have := qlt 0 (by decide); unfold BUFW at *; omega)]
    have buf2 : ∀ t < 3, ∀ q < 4, memoryView c1 (BUFW+82+4*t+q) = memoryView c0 (BUFW+82+4*t+q) := by
      intro t ht q hq; rw [mem1 _ (by unfold BUFW; omega), if_neg (by have := qlt 1 (by decide); unfold BUFW at *; omega)]
    by_cases inside : D ≤ w ∧ w < D+16
    · rw [if_pos inside]
      obtain ⟨j, q, hj, hq, rfl⟩ : ∃ j q, j < 4 ∧ q < 4 ∧ w = D+4*j+q := ⟨(w-D)/4, (w-D)%4, by omega, by omega, by omega⟩
      rw [show (D+4*j+q-D)/4 = j by omega, show (D+4*j+q-D)%4 = q by omega]
      have qd : ∀ t, qslot n t = ((n%4+t+1)%4+4-n%4)%5 := fun t => rfl
      rcases qslot_cases (n%4) j m4 hj with ⟨zero, none⟩ | ⟨nz, hit, tl, others⟩
      · rw [if_pos zero]
        have n2 := none 2 (by decide); have n1 := none 1 (by decide); have n0 := none 0 (by decide)
        change qslot n 2 ≠ j at n2; change qslot n 1 ≠ j at n1; change qslot n 0 ≠ j at n0
        rw [if_neg (by omega), mem1 _ (by omega), if_neg (by omega), mem0 _ (by omega), if_neg (by omega),
          memZ _ (by omega), if_pos ⟨by omega, by omega⟩]
      · rw [if_neg nz]
        have qd' : qslot n (((n%4+j+2)%5+6-n%4)%4) = j := by rw [qd]; exact hit
        generalize ((n%4+j+2)%5+6-n%4)%4 = t at qd' tl others ⊢
        interval_cases t
        · have n1 := others 1 (by decide) (by decide); have n2 := others 2 (by decide) (by decide)
          change qslot n 1 ≠ j at n1; change qslot n 2 ≠ j at n2
          rw [if_neg (by omega), mem1 _ (by omega), if_neg (by omega), mem0 _ (by omega), if_pos ⟨by omega, by omega⟩,
            show D+4*j+q-(D+4*qslot n 0) = q by omega, bufz 0 (by decide) q hq]
        · have n2 := others 2 (by decide) (by decide)
          change qslot n 2 ≠ j at n2
          rw [if_neg (by omega), mem1 _ (by omega), if_pos ⟨by omega, by omega⟩,
            show D+4*j+q-(D+4*qslot n 1) = q by omega, buf1 1 (by decide) q hq, bufz 1 (by decide) q hq]
        · rw [if_pos ⟨by omega, by omega⟩, show D+4*j+q-(D+4*qslot n 2) = q by omega, buf2 2 (by decide) q hq,
            buf1 2 (by decide) q hq, bufz 2 (by decide) q hq]
    · rw [if_neg inside, if_neg (by have := qlt 2 (by decide); omega), mem1 w hw, if_neg (by have := qlt 1 (by decide); omega),
        mem0 w hw, if_neg (by have := qlt 0 (by decide); omega), memZ w hw, if_neg inside]
      simp only [h₆, put_reg_view]

/-! ### 5-ary scratch levels -/

def pentaHeadActs (k n V : Nat) : List Action :=
  [.alu (.REMU .x3 .x22 .x4) .x3 (BitVec.ofNat 64 (n%5)), .alu (.DIVU .x22 .x22 .x4) .x22 (BitVec.ofNat 64 (n/5)),
   .alu (.MUL .x12 .x3 .x1) .x12 (BitVec.ofNat 64 (n%5*5^k)),
   .alu (.ADD .x23 .x23 .x12) .x23 (BitVec.ofNat 64 (V+n%5*5^k)),
   .alu (.MUL .x1 .x1 .x4) .x1 (BitVec.ofNat 64 (5^k*5))]

def upGroupActs (k n : Nat) : List Action :=
  liActs .x11 (HB k + 40) ++ [.alu (.MUL .x12 .x22 .x5) .x12 (BitVec.ofNat 64 (n/5*368)),
    .alu (.ADD .x11 .x11 .x12) .x11 (BitVec.ofNat 64 (HB k + 40 + n/5*368))]

/-- Slot of sibling `j` of node `n` (the other slots of its group, in rotation order). -/
def sibSlot (n j : Nat) : Nat := 5*(n/5)+(n%5+j+1)%5

def sibActs (k D n j : Nat) : List Action :=
  [.offset .x10 .x3 (BitVec.ofNat 12 (j+1)) (BitVec.ofNat 64 (n%5+j+1)),
   .alu (.REMU .x10 .x10 .x4) .x10 (BitVec.ofNat 64 ((n%5+j+1)%5)),
   .alu (.SLLI .x10 .x10 5) .x10 (BitVec.ofNat 64 ((n%5+j+1)%5*2^5)),
   .alu (.ADD .x10 .x10 .x11) .x10 (BitVec.ofNat 64 (8*slotW k (sibSlot n j)))] ++
  copyActs .x10 .x7 0 (32*j) (slotW k (sibSlot n j)) (D+4*j) 4

def sibsActs (k D n m : Nat) : List Action := (List.range m).flatMap (sibActs k D n)

def pentaHighActs (k D n V : Nat) : List Action :=
  pentaHeadActs k n V ++ upGroupActs k n ++ sibsActs k D n 4 ++ [.offset .x7 .x7 128 (BitVec.ofNat 64 (8*D+128))]

theorem sib_acts_op (k D n j : Nat) : (sibActs k D n j).map Action.op = upSibling j := by
  simp only [sibActs, upSibling, List.map_append, copy_acts_op]; rfl

theorem penta_high_op (k D n V : Nat) : (pentaHighActs k D n V).map Action.op = pentaHigh k := by
  have sibs : (sibsActs k D n 4).map Action.op = (List.range 4).flatMap upSibling := by
    simp only [sibsActs, List.map_flatMap, sib_acts_op]
  simp only [pentaHighActs, pentaHigh, upGroup, upGroupActs, List.map_append, li_acts_op, sibs]; rfl

theorem sibs_succ (k D n m : Nat) : sibsActs k D n (m+1) = sibsActs k D n m ++ sibActs k D n m := by
  simp [sibsActs, List.range_succ, List.flatMap_append]

theorem penta_high_free (k D n V : Nat) : PermFree (pentaHighActs k D n V) := by
  have sibs : ∀ m, PermFree (sibsActs k D n m) := by
    intro m
    induction m with
    | zero => intro x hx; simp [sibsActs] at hx
    | succ m ih =>
      rw [sibs_succ]
      refine perm_free_append ih (perm_free_append ?_ (copy_free _ _ _ _ _ _ _))
      intro x hx; simp at hx; rcases hx with h | h | h | h <;> subst h <;> rfl
  refine perm_free_append (perm_free_append (perm_free_append ?_ (perm_free_append (li_free _ _) ?_)) (sibs 4)) ?_
  · intro x hx; simp [pentaHeadActs] at hx; rcases hx with h | h | h | h | h <;> subst h <;> rfl
  · intro x hx; simp at hx; rcases hx with h | h <;> subst h <;> rfl
  · intro x hx; simp at hx; subst hx; rfl

theorem sib_slot_bytes (k n j : Nat) (hk1 : 9 ≤ k) (hk : k ≤ 12) :
    8*slotW k (sibSlot n j) = HB k + 40 + n/5*368 + (n%5+j+1)%5*2^5 := by
  have hb := hb_val k hk1 hk
  have t5 := Nat.mod_lt (n%5+j+1) (show 5 > 0 by decide)
  unfold slotW groupW sibSlot
  rw [show (5*(n/5)+(n%5+j+1)%5)/5 = n/5 by omega, show (5*(n/5)+(n%5+j+1)%5)%5 = (n%5+j+1)%5 by omega]
  omega

/-- One sibling copy. -/
theorem high_sib (o : Oracle) (k D n j : Nat) (s : MachineState) (hk1 : 9 ≤ k) (hk : k ≤ 12) (hj : j < 4)
    (hn : n < pentaCount k) (hD : D + 16 ≤ 2^33) (far : TEND ≤ D)
    (x3 : s.getReg .x3 = BitVec.ofNat 64 (n%5)) (x4 : s.getReg .x4 = BitVec.ofNat 64 5)
    (x11 : s.getReg .x11 = BitVec.ofNat 64 (HB k + 40 + n/5*368)) (x7 : s.getReg .x7 = BitVec.ofNat 64 (8*D)) :
    validFixed o (sibActs k D n j) s ∧
      (∀ r, r ≠ .x10 → r ≠ .x31 → (fixedOps o (sibActs k D n j) s).getReg r = s.getReg r) ∧
      (∀ w < 2^33, memoryView (fixedOps o (sibActs k D n j) s) w =
        if D+4*j ≤ w ∧ w < D+4*j+4 then memoryView s (slotW k (sibSlot n j)+(w-(D+4*j))) else memoryView s w) := by
  have hb := hb_val k hk1 hk
  have cnt := count_penta k hk1 hk
  have gk : n/5 < groups k := by unfold groups; omega
  have m5 : n%5 < 5 := Nat.mod_lt _ (by decide)
  have t5 := Nat.mod_lt (n%5+j+1) (show 5 > 0 by decide)
  have bytes := sib_slot_bytes k n j hk1 hk
  have slotIn : slotW k (sibSlot n j) + 4 ≤ TEND := by
    unfold slotW groupW sibSlot
    rw [show (5*(n/5)+(n%5+j+1)%5)/5 = n/5 by omega, show (5*(n/5)+(n%5+j+1)%5)%5 = (n%5+j+1)%5 by omega]
    omega
  let a := putReg (putReg (putReg (putReg s .x10 (BitVec.ofNat 64 (n%5+j+1))) .x10
    (BitVec.ofNat 64 ((n%5+j+1)%5))) .x10 (BitVec.ofNat 64 ((n%5+j+1)%5*2^5))) .x10
    (BitVec.ofNat 64 (8*slotW k (sibSlot n j)))
  have arithEq : fixedOps o ([.offset .x10 .x3 (BitVec.ofNat 12 (j+1)) (BitVec.ofNat 64 (n%5+j+1)),
      .alu (.REMU .x10 .x10 .x4) .x10 (BitVec.ofNat 64 ((n%5+j+1)%5)),
      .alu (.SLLI .x10 .x10 5) .x10 (BitVec.ofNat 64 ((n%5+j+1)%5*2^5)),
      .alu (.ADD .x10 .x10 .x11) .x10 (BitVec.ofNat 64 (8*slotW k (sibSlot n j)))] : List Action) s = a := rfl
  have akeep : ∀ r, r ≠ .x10 → a.getReg r = s.getReg r := by
    intro r h
    simp only [a]
    rw [put_reg_reg, if_neg (fun hh => h hh.1.symm), put_reg_reg, if_neg (fun hh => h hh.1.symm), put_reg_reg,
      if_neg (fun hh => h hh.1.symm), put_reg_reg, if_neg (fun hh => h hh.1.symm)]
  have a10 : a.getReg .x10 = BitVec.ofNat 64 (8*slotW k (sibSlot n j)) := by
    simp only [a]; rw [put_reg_reg, if_pos ⟨rfl, by decide⟩]
  have arith : validFixed o ([.offset .x10 .x3 (BitVec.ofNat 12 (j+1)) (BitVec.ofNat 64 (n%5+j+1)),
      .alu (.REMU .x10 .x10 .x4) .x10 (BitVec.ofNat 64 ((n%5+j+1)%5)),
      .alu (.SLLI .x10 .x10 5) .x10 (BitVec.ofNat 64 ((n%5+j+1)%5*2^5)),
      .alu (.ADD .x10 .x10 .x11) .x10 (BitVec.ofNat 64 (8*slotW k (sibSlot n j)))] : List Action) s := by
    refine ⟨?_, ?_, ?_, ?_, trivial⟩
    · show s.getReg .x3 + signExtend12 (BitVec.ofNat 12 (j+1)) = _
      rw [x3, add_small _ _ (by omega) (by omega)]; congr 1
    · apply alu_remu
      simp only [fixedStep, put_reg_reg, ne_eq, reduceCtorEq, false_and, if_false, not_false_eq_true, and_self,
        if_true]
      rw [x4, word_remu _ _ (by omega) (by decide) (by decide)]
    · apply alu_slli
      simp only [fixedStep, put_reg_reg, ne_eq, reduceCtorEq, false_and, if_false, not_false_eq_true, and_self,
        if_true]
      rw [show (5 : BitVec 6).toNat = 5 from rfl, word_shl _ _ (by omega)]
    · apply alu_add
      simp only [fixedStep, put_reg_reg, ne_eq, reduceCtorEq, false_and, if_false, not_false_eq_true, and_self,
        if_true]
      rw [x11, word_add _ _ (by unfold TEND at *; omega)]
      congr 1; omega
  have a7 : a.getReg .x7 = BitVec.ofNat 64 (8*D) := (akeep .x7 (by decide)).trans x7
  obtain ⟨okC, regsC, memC⟩ := copy_run o a .x10 .x7 (by decide) (by decide) 0 (32*j) (slotW k (sibSlot n j))
    (D+4*j) 4 (8*slotW k (sibSlot n j)) (8*D) a10 a7 (by omega) (by omega) (by decide) (by omega)
    (by unfold TEND at *; omega) (by omega) (Or.inl (by omega))
  have fin : fixedOps o (sibActs k D n j) s = fixedOps o (copyActs .x10 .x7 0 (32*j) (slotW k (sibSlot n j)) (D+4*j) 4) a := by
    unfold sibActs; rw [fixedOps_append, arithEq]
  have aview : memoryView a = memoryView s := by simp only [a, put_reg_view]
  refine ⟨?_, ?_, ?_⟩
  · unfold sibActs; rw [validFixed_append, arithEq]; exact ⟨arith, okC⟩
  · intro r h10 h31; rw [fin, regsC r h31, akeep r h10]
  · intro w hw; rw [fin, memC w hw, aview]

/-- The first `m` sibling copies. -/
theorem high_sibs (o : Oracle) (k D n : Nat) (s : MachineState) (hk1 : 9 ≤ k) (hk : k ≤ 12)
    (hn : n < pentaCount k) (hD : D + 16 ≤ 2^33) (far : TEND ≤ D)
    (x3 : s.getReg .x3 = BitVec.ofNat 64 (n%5)) (x4 : s.getReg .x4 = BitVec.ofNat 64 5)
    (x11 : s.getReg .x11 = BitVec.ofNat 64 (HB k + 40 + n/5*368)) (x7 : s.getReg .x7 = BitVec.ofNat 64 (8*D)) :
    ∀ m ≤ 4, validFixed o (sibsActs k D n m) s ∧
      (∀ r, r ≠ .x10 → r ≠ .x31 → (fixedOps o (sibsActs k D n m) s).getReg r = s.getReg r) ∧
      (∀ w < 2^33, memoryView (fixedOps o (sibsActs k D n m) s) w =
        if D ≤ w ∧ w < D+4*m then memoryView s (slotW k (sibSlot n ((w-D)/4))+(w-D)%4) else memoryView s w) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨trivial, fun r _ _ => rfl, fun w _ => ?_⟩
    rw [if_neg (by omega)]; rfl
  | succ m ih =>
    intro hm
    obtain ⟨ok, regs, mem⟩ := ih (by omega)
    rw [sibs_succ, validFixed_append, fixedOps_append]
    generalize ht : fixedOps o (sibsActs k D n m) s = t at ok regs mem
    obtain ⟨okS, regsS, memS⟩ := high_sib o k D n m t hk1 hk (by omega) hn hD far
      ((regs .x3 (by decide) (by decide)).trans x3) ((regs .x4 (by decide) (by decide)).trans x4)
      ((regs .x11 (by decide) (by decide)).trans x11) ((regs .x7 (by decide) (by decide)).trans x7)
    have hb := hb_val k hk1 hk
    have slotIn : ∀ j, slotW k (sibSlot n j) + 4 ≤ TEND := by
      intro j
      have cnt := count_penta k hk1 hk
      have gk : n/5 < groups k := by unfold groups; omega
      have t5 := Nat.mod_lt (n%5+j+1) (show 5 > 0 by decide)
      unfold slotW groupW sibSlot
      rw [show (5*(n/5)+(n%5+j+1)%5)/5 = n/5 by omega, show (5*(n/5)+(n%5+j+1)%5)%5 = (n%5+j+1)%5 by omega]
      omega
    refine ⟨⟨ok, okS⟩, fun r a b => by rw [regsS r a b, regs r a b], ?_⟩
    intro w hw
    rw [memS w hw]
    by_cases blk : D+4*m ≤ w ∧ w < D+4*m+4
    · rw [if_pos blk, if_pos ⟨by omega, by omega⟩, mem _ (by have := slotIn m; unfold TEND at *; omega),
        if_neg (by have := slotIn m; omega)]
      rw [show (w-D)/4 = m by omega, show w-(D+4*m) = (w-D)%4 by omega]
    · rw [if_neg blk, mem w hw]
      by_cases old : D ≤ w ∧ w < D+4*m
      · rw [if_pos old, if_pos ⟨old.1, by omega⟩]
      · rw [if_neg old, if_neg (by omega)]

theorem high_li : ∀ k, 9 ≤ k → k ≤ 12 → LiOK (HB k + 40) := by
  intro k h1 h2; interval_cases k <;> decide

theorem penta_high (o : Oracle) (k D n V : Nat) (s : MachineState) (hk1 : 9 ≤ k) (hk : k ≤ 12) (pre : LevelPre k D n V s)
    (hn : n < pentaCount k) (hV : V < 5^k) (hD : D + 16 ≤ 2^33) (far : TEND ≤ D) :
    validFixed o (pentaHighActs k D n V) s ∧
      LevelPre (k+1) (D+16) (n/5) (V+n%5*5^k) (fixedOps o (pentaHighActs k D n V) s) ∧
      (∀ r, LevelKept r → (fixedOps o (pentaHighActs k D n V) s).getReg r = s.getReg r) ∧
      (∀ w < 2^33, memoryView (fixedOps o (pentaHighActs k D n V) s) w =
        if D ≤ w ∧ w < D+16 then memoryView s (slotW k (sibSlot n ((w-D)/4))+(w-D)%4) else memoryView s w) := by
  have hb := hb_val k hk1 hk
  have cnt := count_penta k hk1 hk
  have hn' : n < 2^40 := by
    have : pentaCount k ≤ 263 := by rw [← cnt]; interval_cases k <;> decide
    omega
  have p5 : 5^k ≤ 5^12 := Nat.pow_le_pow_right (by decide) hk
  have p16 : (5:Nat)^12 = 244140625 := by norm_num
  have m5 : n%5 < 5 := Nat.mod_lt _ (by decide)
  have bound12 : n%5*5^k ≤ 4*5^k := Nat.mul_le_mul_right _ (by omega)
  -- the head
  let h₅ := putReg (putReg (putReg (putReg (putReg s .x3 (BitVec.ofNat 64 (n%5))) .x22 (BitVec.ofNat 64 (n/5)))
    .x12 (BitVec.ofNat 64 (n%5*5^k))) .x23 (BitVec.ofNat 64 (V+n%5*5^k))) .x1 (BitVec.ofNat 64 (5^k*5))
  have headEq : fixedOps o (pentaHeadActs k n V) s = h₅ := rfl
  have keep₅ : ∀ r, r ≠ .x3 → r ≠ .x22 → r ≠ .x12 → r ≠ .x23 → r ≠ .x1 → h₅.getReg r = s.getReg r := by
    intro r a b c d e
    simp only [h₅]
    rw [put_reg_reg, if_neg (fun h => e h.1.symm), put_reg_reg, if_neg (fun h => d h.1.symm), put_reg_reg,
      if_neg (fun h => c h.1.symm), put_reg_reg, if_neg (fun h => b h.1.symm), put_reg_reg, if_neg (fun h => a h.1.symm)]
  have head : validFixed o (pentaHeadActs k n V) s := by
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
  have g3 : h₅.getReg .x3 = BitVec.ofNat 64 (n%5) := by
    simp only [h₅]; rw [put_reg_reg, if_neg (by decide), put_reg_reg, if_neg (by decide), put_reg_reg,
      if_neg (by decide), put_reg_reg, if_neg (by decide), put_reg_reg, if_pos ⟨rfl, by decide⟩]
  have g22 : h₅.getReg .x22 = BitVec.ofNat 64 (n/5) := by
    simp only [h₅]; rw [put_reg_reg, if_neg (by decide), put_reg_reg, if_neg (by decide), put_reg_reg,
      if_neg (by decide), put_reg_reg, if_pos ⟨rfl, by decide⟩]
  have g23 : h₅.getReg .x23 = BitVec.ofNat 64 (V+n%5*5^k) := by
    simp only [h₅]; rw [put_reg_reg, if_neg (by decide), put_reg_reg, if_pos ⟨rfl, by decide⟩]
  have g1 : h₅.getReg .x1 = BitVec.ofNat 64 (5^k*5) := by simp only [h₅]; rw [put_reg_reg, if_pos ⟨rfl, by decide⟩]
  -- the group base
  obtain ⟨okL, x11L, keepL, viewL⟩ := li_run o h₅ .x11 (HB k + 40) (high_li k hk1 hk) (by decide)
  generalize hl : fixedOps o (liActs .x11 (HB k + 40)) h₅ = l at okL x11L keepL viewL
  have l22 : l.getReg .x22 = BitVec.ofNat 64 (n/5) := (keepL .x22 (by decide)).trans g22
  have l5 : l.getReg .x5 = BitVec.ofNat 64 368 := by
    rw [keepL .x5 (by decide), keep₅ .x5 (by decide) (by decide) (by decide) (by decide) (by decide), pre.x5]
  have gk : n/5 < groups k := by unfold groups; omega
  let g := putReg (putReg l .x12 (BitVec.ofNat 64 (n/5*368))) .x11 (BitVec.ofNat 64 (HB k + 40 + n/5*368))
  have grpOK : validFixed o [.alu (.MUL .x12 .x22 .x5) .x12 (BitVec.ofNat 64 (n/5*368)),
      .alu (.ADD .x11 .x11 .x12) .x11 (BitVec.ofNat 64 (HB k + 40 + n/5*368))] l := by
    refine ⟨?_, ?_, trivial⟩
    · apply alu_mul; rw [l22, l5, word_mul _ _ (by omega) (by decide)]
    · apply alu_add
      simp only [fixedStep, put_reg_reg, ne_eq, reduceCtorEq, false_and, if_false, not_false_eq_true, and_self,
        if_true]
      rw [x11L, word_add _ _ (by unfold TEND at *; omega)]
  have grpEq : fixedOps o [.alu (.MUL .x12 .x22 .x5) .x12 (BitVec.ofNat 64 (n/5*368)),
      .alu (.ADD .x11 .x11 .x12) .x11 (BitVec.ofNat 64 (HB k + 40 + n/5*368))] l = g := rfl
  have gkeep : ∀ r, r ≠ .x11 → r ≠ .x12 → g.getReg r = l.getReg r := by
    intro r a b
    simp only [g]
    rw [put_reg_reg, if_neg (fun hh => a hh.1.symm), put_reg_reg, if_neg (fun hh => b hh.1.symm)]
  have g11 : g.getReg .x11 = BitVec.ofNat 64 (HB k + 40 + n/5*368) := by
    simp only [g]; rw [put_reg_reg, if_pos ⟨rfl, by decide⟩]
  have gview : memoryView g = memoryView s := by simp only [g, put_reg_view]; rw [viewL]; simp only [h₅, put_reg_view]
  have chain : ∀ r, r ≠ .x11 → r ≠ .x12 → r ≠ .x3 → r ≠ .x22 → r ≠ .x23 → r ≠ .x1 → g.getReg r = s.getReg r := by
    intro r a b c d e f
    rw [gkeep r a b, keepL r a, keep₅ r c d b e f]
  have g3' : g.getReg .x3 = BitVec.ofNat 64 (n%5) := by
    rw [gkeep _ (by decide) (by decide), keepL _ (by decide), g3]
  have g4 : g.getReg .x4 = BitVec.ofNat 64 5 := by
    rw [chain _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), pre.x4]
  have g7 : g.getReg .x7 = BitVec.ofNat 64 (8*D) := by
    rw [chain _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), pre.x7]
  -- the siblings
  obtain ⟨okS, regsS, memS⟩ := high_sibs o k D n g hk1 hk hn hD far g3' g4 g11 g7 4 le_rfl
  generalize hsb : fixedOps o (sibsActs k D n 4) g = b at okS regsS memS
  have b7 : b.getReg .x7 = BitVec.ofNat 64 (8*D) := by rw [regsS _ (by decide) (by decide), g7]
  have split : pentaHighActs k D n V = pentaHeadActs k n V ++ (liActs .x11 (HB k + 40) ++
      [.alu (.MUL .x12 .x22 .x5) .x12 (BitVec.ofNat 64 (n/5*368)),
       .alu (.ADD .x11 .x11 .x12) .x11 (BitVec.ofNat 64 (HB k + 40 + n/5*368))]) ++ sibsActs k D n 4 ++
      [.offset .x7 .x7 128 (BitVec.ofNat 64 (8*D+128))] := rfl
  have fin : fixedOps o (pentaHighActs k D n V) s = putReg b .x7 (BitVec.ofNat 64 (8*D+128)) := by
    rw [split, fixedOps_append, fixedOps_append, fixedOps_append, headEq, fixedOps_append, hl, grpEq, hsb]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · have midEq : fixedOps o (pentaHeadActs k n V ++ (liActs .x11 (HB k + 40) ++
        [.alu (.MUL .x12 .x22 .x5) .x12 (BitVec.ofNat 64 (n/5*368)),
         .alu (.ADD .x11 .x11 .x12) .x11 (BitVec.ofNat 64 (HB k + 40 + n/5*368))])) s = g := by
      rw [fixedOps_append, headEq, fixedOps_append, hl, grpEq]
    have midOK : validFixed o (pentaHeadActs k n V ++ (liActs .x11 (HB k + 40) ++
        [.alu (.MUL .x12 .x22 .x5) .x12 (BitVec.ofNat 64 (n/5*368)),
         .alu (.ADD .x11 .x11 .x12) .x11 (BitVec.ofNat 64 (HB k + 40 + n/5*368))])) s := by
      rw [validFixed_append, headEq, validFixed_append, hl]; exact ⟨head, okL, grpOK⟩
    have split2 : pentaHighActs k D n V = (pentaHeadActs k n V ++ (liActs .x11 (HB k + 40) ++
        [.alu (.MUL .x12 .x22 .x5) .x12 (BitVec.ofNat 64 (n/5*368)),
         .alu (.ADD .x11 .x11 .x12) .x11 (BitVec.ofNat 64 (HB k + 40 + n/5*368))])) ++ sibsActs k D n 4 ++
        [.offset .x7 .x7 128 (BitVec.ofNat 64 (8*D+128))] := rfl
    generalize (pentaHeadActs k n V ++ (liActs .x11 (HB k + 40) ++
        [.alu (.MUL .x12 .x22 .x5) .x12 (BitVec.ofNat 64 (n/5*368)),
         .alu (.ADD .x11 .x11 .x12) .x11 (BitVec.ofNat 64 (HB k + 40 + n/5*368))])) = M at midEq midOK split2
    rw [split2, validFixed_append, validFixed_append, fixedOps_append, midEq, hsb]
    refine ⟨⟨midOK, okS⟩, ?_, trivial⟩
    show b.getReg .x7 + _ = _
    rw [b7, show (128 : BitVec 12) = BitVec.ofNat 12 128 from rfl, add_small _ 128 (by decide) (by omega)]
  · rw [fin]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [put_reg_reg]
    · rw [if_pos ⟨rfl, by decide⟩]; congr 1
    · rw [if_neg (by decide), regsS _ (by decide) (by decide),
        chain _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), pre.x20]
    · rw [if_neg (by decide), regsS _ (by decide) (by decide), gkeep _ (by decide) (by decide), l22]
    · rw [if_neg (by decide), regsS _ (by decide) (by decide), gkeep _ (by decide) (by decide), keepL _ (by decide), g23]
    · rw [if_neg (by decide), regsS _ (by decide) (by decide), gkeep _ (by decide) (by decide), keepL _ (by decide), g1,
        pow_succ]
    · rw [if_neg (by decide), regsS _ (by decide) (by decide), g4]
    · rw [if_neg (by decide), regsS _ (by decide) (by decide),
        chain _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), pre.x30]
    · rw [if_neg (by decide), regsS _ (by decide) (by decide),
        chain _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), pre.x5]
  · intro r kept
    obtain ⟨a, b', c, d, e, f, gg, h, i, j⟩ := kept
    rw [fin, put_reg_reg, if_neg (fun hh => d hh.1.symm), regsS r e j, chain r f gg b' h i a]
  · intro w hw
    rw [fin, put_reg_view, memS w hw, gview]

end TwoPermutationPrototype.HybWrap
