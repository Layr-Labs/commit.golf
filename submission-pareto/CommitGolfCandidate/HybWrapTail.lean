import CommitGolfCandidate.HybWrapRecord

/-! The expansion setup (words 2035-2050), the record loop, and the tail (words 3287-4013): 343 words
past the records cleared, `x17 = 1944k`, `x6 = 2200`, `x10-x15` restored, every temporary zeroed,
jump to word 1. -/

namespace TwoPermutationPrototype.HybWrap
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp
open TwoPermutationPrototype.RV64 TwoPermutationPrototype.Checker TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.CheckActions
open TwoPermutationPrototype.PentaWrap (loaderReg loader_reg proof_word proofWord)
open TwoPermutationPrototype.Quad.Checker (loaderReference packedImage)

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

/-! ### Expansion setup -/

theorem exp_codes : WrapAt 1291 expSetup := by decide

def expA (k : Nat) : List Action :=
  [.offset .x31 .x16 4095 (BitVec.ofNat 64 (k-1)), .offset .x8 .x0 720 (BitVec.ofNat 64 720),
   .alu (.MUL .x8 .x31 .x8) .x8 (BitVec.ofNat 64 ((k-1)*720)),
   .alu (.ADD .x8 .x29 .x8) .x8 (BitVec.ofNat 64 (PB+720*k-720))]

def expB (k : Nat) : List Action :=
  [.alu (.MUL .x9 .x31 .x9) .x9 (BitVec.ofNat 64 ((k-1)*2200)),
   .alu (.ADD .x9 .x29 .x9) .x9 (BitVec.ofNat 64 (PB+2200*k-2200)),
   .alu (.SLLI .x18 .x31 3) .x18 (BitVec.ofNat 64 ((k-1)*2^3)),
   .alu (.ADD .x18 .x27 .x18) .x18 (BitVec.ofNat 64 (IDXB+8*k-8)),
   .offset .x19 .x16 0 (BitVec.ofNat 64 k)]

def expC : List Action :=
  [.offset .x4 .x0 5 (BitVec.ofNat 64 5), .offset .x30 .x0 96 (BitVec.ofNat 64 96),
   .offset .x5 .x0 368 (BitVec.ofNat 64 368)]

def expActs (k : Nat) : List Action := expA k ++ liActs .x9 2200 ++ expB k ++ liActs .x20 BUF ++ expC

theorem exp_acts_op (k : Nat) : (expActs k).map Action.op = expSetup := rfl

theorem exp_free (k : Nat) : PermFree (expActs k) := by
  unfold expActs
  refine perm_free_append (perm_free_append (perm_free_append (perm_free_append ?_ (li_free _ _)) ?_) (li_free _ _)) ?_
  · intro x hx; simp [expA] at hx; rcases hx with h | h | h | h <;> subst h <;> rfl
  · intro x hx; simp [expB] at hx; rcases hx with h | h | h | h | h <;> subst h <;> rfl
  · intro x hx; simp [expC] at hx; rcases hx with h | h | h <;> subst h <;> rfl

/-- Registers the setup reads, in the state after the hashes. -/
structure SetupRegs (k : Nat) (u : MachineState) : Prop where
  x16 : u.getReg .x16 = BitVec.ofNat 64 k
  x29 : u.getReg .x29 = BitVec.ofNat 64 PB
  x27 : u.getReg .x27 = BitVec.ofNat 64 IDXB

def ExpTouched (x : Reg) : Prop :=
  x = .x31 ∨ x = .x8 ∨ x = .x9 ∨ x = .x18 ∨ x = .x19 ∨ x = .x20 ∨ x = .x4 ∨ x = .x30 ∨ x = .x5

theorem exp_setup (o : Oracle) (k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ 16777216) (u : MachineState) (regs : SetupRegs k u) :
    let v := fixedOps o (expActs k) u
    validFixed o (expActs k) u ∧ memoryView v = memoryView u ∧
      v.getReg .x8 = BitVec.ofNat 64 (PB+720*k-720) ∧ v.getReg .x9 = BitVec.ofNat 64 (PB+2200*k-2200) ∧
      v.getReg .x18 = BitVec.ofNat 64 (IDXB+8*k-8) ∧ v.getReg .x19 = BitVec.ofNat 64 k ∧
      v.getReg .x20 = BitVec.ofNat 64 BUF ∧ v.getReg .x4 = BitVec.ofNat 64 5 ∧ v.getReg .x30 = BitVec.ofNat 64 96 ∧
      v.getReg .x5 = BitVec.ofNat 64 368 ∧ (∀ x, ¬ ExpTouched x → v.getReg x = u.getReg x) := by
  intro v
  -- block A
  let a := putReg (putReg (putReg (putReg u .x31 (BitVec.ofNat 64 (k-1))) .x8 (BitVec.ofNat 64 720)) .x8
    (BitVec.ofNat 64 ((k-1)*720))) .x8 (BitVec.ofNat 64 (PB+720*k-720))
  have aEq : fixedOps o (expA k) u = a := rfl
  have okA : validFixed o (expA k) u := by
    refine ⟨?_, ?_, ?_, ?_, trivial⟩
    · show u.getReg .x16 + _ = _
      rw [regs.x16, show (4095 : BitVec 12) = BitVec.ofNat 12 4095 from rfl,
        add_neg k 4095 (by decide) (by decide) (by omega) (by omega)]
    · show (putReg u .x31 _).getReg .x0 + _ = _; rw [reg_zero]; decide
    · apply alu_mul
      simp only [fixedStep, put_reg_reg, ne_eq, reduceCtorEq, false_and, if_false, not_false_eq_true, and_self, if_true]
      rw [word_mul _ _ (by omega) (by decide)]
    · apply alu_add
      simp only [fixedStep, put_reg_reg, ne_eq, reduceCtorEq, false_and, if_false, not_false_eq_true, and_self, if_true]
      rw [regs.x29, word_add _ _ (by unfold PB; omega)]
      congr 1; unfold PB; omega
  have aKeep : ∀ x, x ≠ .x31 → x ≠ .x8 → a.getReg x = u.getReg x := by
    intro x h1 h2
    simp only [a]
    rw [put_reg_reg, if_neg (fun h => h2 h.1.symm), put_reg_reg, if_neg (fun h => h2 h.1.symm), put_reg_reg,
      if_neg (fun h => h2 h.1.symm), put_reg_reg, if_neg (fun h => h1 h.1.symm)]
  have a31 : a.getReg .x31 = BitVec.ofNat 64 (k-1) := by
    simp only [a, put_reg_reg, ne_eq, reduceCtorEq, false_and, if_false, not_false_eq_true, and_self, if_true]
  have a8 : a.getReg .x8 = BitVec.ofNat 64 (PB+720*k-720) := by
    simp only [a, put_reg_reg, ne_eq, reduceCtorEq, false_and, if_false, not_false_eq_true, and_self, if_true]
  -- li x9
  obtain ⟨ok9, x9₁, keep9, view9⟩ := li_run o a .x9 2200 (by decide) (by decide)
  generalize hb : fixedOps o (liActs .x9 2200) a = b at ok9 x9₁ keep9 view9
  -- block B
  let c := putReg (putReg (putReg (putReg (putReg b .x9 (BitVec.ofNat 64 ((k-1)*2200))) .x9
    (BitVec.ofNat 64 (PB+2200*k-2200))) .x18 (BitVec.ofNat 64 ((k-1)*2^3))) .x18 (BitVec.ofNat 64 (IDXB+8*k-8))) .x19
    (BitVec.ofNat 64 k)
  have cEq : fixedOps o (expB k) b = c := rfl
  have b31 : b.getReg .x31 = BitVec.ofNat 64 (k-1) := by rw [keep9 _ (by decide), a31]
  have b29 : b.getReg .x29 = BitVec.ofNat 64 PB := by
    rw [keep9 _ (by decide), aKeep _ (by decide) (by decide), regs.x29]
  have b27 : b.getReg .x27 = BitVec.ofNat 64 IDXB := by
    rw [keep9 _ (by decide), aKeep _ (by decide) (by decide), regs.x27]
  have b16 : b.getReg .x16 = BitVec.ofNat 64 k := by
    rw [keep9 _ (by decide), aKeep _ (by decide) (by decide), regs.x16]
  have okB : validFixed o (expB k) b := by
    refine ⟨?_, ?_, ?_, ?_, ?_, trivial⟩
    · apply alu_mul; rw [b31, x9₁, word_mul _ _ (by omega) (by decide)]
    · apply alu_add
      simp only [fixedStep, put_reg_reg, ne_eq, reduceCtorEq, false_and, if_false, not_false_eq_true, and_self, if_true]
      rw [b29, word_add _ _ (by unfold PB; omega)]
      congr 1; unfold PB; omega
    · apply alu_slli
      simp only [fixedStep, put_reg_reg, ne_eq, reduceCtorEq, false_and, if_false]
      rw [b31, show (3 : BitVec 6).toNat = 3 from rfl, word_shl _ _ (by omega)]
    · apply alu_add
      simp only [fixedStep, put_reg_reg, ne_eq, reduceCtorEq, false_and, if_false, not_false_eq_true, and_self, if_true]
      rw [b27, word_add _ _ (by unfold IDXB; omega)]
      congr 1; unfold IDXB; omega
    · show (putReg (putReg (putReg (putReg b .x9 _) .x9 _) .x18 _) .x18 _).getReg .x16 + _ = _
      simp only [put_reg_reg, ne_eq, reduceCtorEq, false_and, if_false]
      rw [b16, show (0 : BitVec 12) = BitVec.ofNat 12 0 from rfl, add_small _ 0 (by decide) (by omega)]; rfl
  have cKeep : ∀ x, x ≠ .x9 → x ≠ .x18 → x ≠ .x19 → c.getReg x = b.getReg x := by
    intro x h9 h18 h19
    simp only [c]
    rw [put_reg_reg, if_neg (fun h => h19 h.1.symm), put_reg_reg, if_neg (fun h => h18 h.1.symm), put_reg_reg,
      if_neg (fun h => h18 h.1.symm), put_reg_reg, if_neg (fun h => h9 h.1.symm), put_reg_reg,
      if_neg (fun h => h9 h.1.symm)]
  -- li x20
  obtain ⟨ok20, x20₁, keep20, view20⟩ := li_run o c .x20 BUF (by decide) (by decide)
  generalize hd : fixedOps o (liActs .x20 BUF) c = d at ok20 x20₁ keep20 view20
  let f := putReg (putReg (putReg d .x4 (BitVec.ofNat 64 5)) .x30 (BitVec.ofNat 64 96)) .x5 (BitVec.ofNat 64 368)
  have fEq : fixedOps o expC d = f := rfl
  have okC : validFixed o expC d := by
    refine ⟨?_, ?_, ?_, trivial⟩
    · show d.getReg .x0 + _ = _; rw [reg_zero]; decide
    · show (putReg d .x4 _).getReg .x0 + _ = _; rw [reg_zero]; decide
    · show (putReg (putReg d .x4 _) .x30 _).getReg .x0 + _ = _; rw [reg_zero]; decide
  have vEq : v = f := by
    show fixedOps o (expActs k) u = f
    unfold expActs
    rw [fixedOps_append, fixedOps_append, fixedOps_append, fixedOps_append, aEq, hb, cEq, hd, fEq]
  have fKeep : ∀ x, x ≠ .x4 → x ≠ .x30 → x ≠ .x5 → f.getReg x = d.getReg x := by
    intro x h4 h30 h5
    simp only [f]
    rw [put_reg_reg, if_neg (fun h => h5 h.1.symm), put_reg_reg, if_neg (fun h => h30 h.1.symm), put_reg_reg,
      if_neg (fun h => h4 h.1.symm)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold expActs
    simp only [validFixed_append, fixedOps_append, aEq, hb, cEq, hd]
    exact ⟨⟨⟨⟨okA, ok9⟩, okB⟩, ok20⟩, okC⟩
  · rw [vEq]; simp only [f, put_reg_view]; rw [view20]; simp only [c, put_reg_view]; rw [view9]
    simp only [a, put_reg_view]
  · rw [vEq, fKeep _ (by decide) (by decide) (by decide), keep20 _ (by decide), cKeep _ (by decide) (by decide)
      (by decide), keep9 _ (by decide), a8]
  · rw [vEq, fKeep _ (by decide) (by decide) (by decide), keep20 _ (by decide)]
    simp only [c, put_reg_reg, ne_eq, reduceCtorEq, false_and, if_false, not_false_eq_true, and_self, if_true]
  · rw [vEq, fKeep _ (by decide) (by decide) (by decide), keep20 _ (by decide)]
    simp only [c, put_reg_reg, ne_eq, reduceCtorEq, false_and, if_false, not_false_eq_true, and_self, if_true]
  · rw [vEq, fKeep _ (by decide) (by decide) (by decide), keep20 _ (by decide)]
    simp only [c, put_reg_reg, ne_eq, reduceCtorEq, false_and, if_false, not_false_eq_true, and_self, if_true]
  · rw [vEq, fKeep _ (by decide) (by decide) (by decide), x20₁]
  · rw [vEq]; simp only [f, put_reg_reg, ne_eq, reduceCtorEq, false_and, if_false, not_false_eq_true, and_self, if_true]
  · rw [vEq]; simp only [f, put_reg_reg, ne_eq, reduceCtorEq, false_and, if_false, not_false_eq_true, and_self, if_true]
  · rw [vEq]; simp only [f, put_reg_reg, ne_eq, reduceCtorEq, false_and, if_false, not_false_eq_true, and_self, if_true]
  · intro x nt
    unfold ExpTouched at nt
    rw [vEq, fKeep x (by tauto) (by tauto) (by tauto), keep20 x (by tauto), cKeep x (by tauto) (by tauto) (by tauto),
      keep9 x (by tauto), aKeep x (by tauto) (by tauto)]

/-! ### The record loop -/

theorem rec_loop (o : Oracle) (input : CheckInput) (e : MachineState) (t₀ : MachineState)
    (mem₀ : RecMem o input e input.positions.card t₀) (pc₀ : t₀.pc = BitVec.ofNat 64 (4096+4*(464+1307)))
    (pos : input.positions.card ≠ 0) :
    ∀ i ≤ input.positions.card, ∃ t cycles, Obs o packedImage t₀ t (872*i) cycles 0 [] ∧
      RecMem o input e (input.positions.card - i) t ∧
      t.pc = BitVec.ofNat 64 (4096+4*(464+(if input.positions.card - i = 0 then 2179 else 1307))) := by
  intro i
  induction i with
  | zero => intro _; exact ⟨t₀, 0, by simpa using Obs.refl o packedImage t₀, mem₀, by rw [if_neg (by omega)]; exact pc₀⟩
  | succ i ih =>
    intro hi
    obtain ⟨t, c, obs, mem, pc⟩ := ih (by omega)
    rw [if_neg (by omega)] at pc
    obtain ⟨t', c', step, mem', pc'⟩ := record_step o input e (input.positions.card - i) (by omega) (by omega) t mem pc
    rw [show input.positions.card - i - 1 = input.positions.card - (i+1) by omega] at mem' pc'
    exact ⟨t', _, (obs.trans step).cast (by ring) rfl rfl rfl, mem', pc'⟩

/-! ### The tail -/

theorem tail_codes_a : WrapAt 2179 (liCode .x17 2200 ++ [.MUL .x17 .x16 .x17, .ADD .x6 .x29 .x17]) := by decide
set_option maxHeartbeats 8000000 in
theorem tail_codes_z1 : WrapAt 2183 (zeroStores .x6 255) := by decide
set_option maxHeartbeats 8000000 in
theorem tail_codes_z2 : WrapAt 2439 (zeroStores .x6 88) := by decide
theorem tail_codes_b : wrapCode[2438]? = some (.ADDI .x6 .x6 2040) := by decide
theorem tail_codes_r : WrapAt 2527 (liCode .x6 2200 ++ restoreRegs ++ zeroedRegs.map (fun r => .ADDI r .x0 0)) ∧
    wrapCode[2556]? = some (.JAL .x0 2085076) := by decide

theorem tail_codes : WrapAt 2179 (liCode .x17 2200 ++ [.MUL .x17 .x16 .x17, .ADD .x6 .x29 .x17]) ∧
    WrapAt 2183 (zeroStores .x6 255) ∧ wrapCode[2438]? = some (.ADDI .x6 .x6 2040) ∧ WrapAt 2439 (zeroStores .x6 88) ∧
    WrapAt 2527 (liCode .x6 2200 ++ restoreRegs ++ zeroedRegs.map (fun r => .ADDI r .x0 0)) ∧
    wrapCode[2556]? = some (.JAL .x0 2085076) :=
  ⟨tail_codes_a, tail_codes_z1, tail_codes_b, tail_codes_z2, tail_codes_r.1, tail_codes_r.2⟩

def tailA (k : Nat) : List Action :=
  liActs .x17 2200 ++ [.alu (.MUL .x17 .x16 .x17) .x17 (BitVec.ofNat 64 (k*2200)),
    .alu (.ADD .x6 .x29 .x17) .x6 (BitVec.ofNat 64 (PB+k*2200))]

def restoreActs : List Action :=
  [.offset .x10 .x24 0 (BitVec.ofNat 64 4096), .offset .x11 .x25 0 (BitVec.ofNat 64 4294971392),
   .offset .x12 .x26 0 (BitVec.ofNat 64 4294971424), .offset .x13 .x27 0 (BitVec.ofNat 64 6375350304),
   .offset .x14 .x28 0 (BitVec.ofNat 64 6509568096), .offset .x15 .x29 0 (BitVec.ofNat 64 PB)]

def zeroRegActs (l : List Reg) : List Action := l.map fun r => .offset r .x0 0 (BitVec.ofNat 64 0)

def tailB : List Action := liActs .x6 2200 ++ restoreActs ++ zeroRegActs zeroedRegs

theorem zero_regs_run (o : Oracle) : ∀ (l : List Reg) (s : MachineState),
    validFixed o (zeroRegActs l) s ∧
      (∀ x, (fixedOps o (zeroRegActs l) s).getReg x = if x ∈ l ∧ x ≠ .x0 then 0 else s.getReg x) ∧
      memoryView (fixedOps o (zeroRegActs l) s) = memoryView s
  | [], s => ⟨trivial, fun x => by simp [zeroRegActs, fixedOps], rfl⟩
  | r :: rest, s => by
    obtain ⟨ok, regs, view⟩ := zero_regs_run o rest (putReg s r (BitVec.ofNat 64 0))
    refine ⟨⟨by show s.getReg .x0 + _ = _; rw [reg_zero]; decide, ok⟩, ?_, ?_⟩
    · intro x
      show (fixedOps o (zeroRegActs rest) (putReg s r _)).getReg x = _
      rw [regs, put_reg_reg]
      by_cases hx : x ∈ rest ∧ x ≠ .x0
      · rw [if_pos hx, if_pos ⟨List.mem_cons_of_mem _ hx.1, hx.2⟩]
      · rw [if_neg hx]
        by_cases same : r = x ∧ r ≠ .x0
        · rw [if_pos same, if_pos ⟨by rw [same.1]; exact List.mem_cons_self .., by rw [← same.1]; exact same.2⟩]; rfl
        · rw [if_neg same]
          by_cases z : x = .x0
          · subst z; simp
          · have : x ∉ rest := fun h => hx ⟨h, z⟩
            have : r ≠ x := fun h => same ⟨h, by rw [h]; exact z⟩
            rw [if_neg (by simp; tauto)]
    · show memoryView (fixedOps o (zeroRegActs rest) (putReg s r _)) = _
      rw [view, put_reg_view]

theorem zero_regs_op (l : List Reg) : (zeroRegActs l).map Action.op = l.map (fun r => .ADDI r .x0 0) := by
  simp only [zeroRegActs, List.map_map]
  apply List.map_congr_left
  intro a _; rfl

theorem tail_free (k : Nat) : PermFree (tailA k) ∧ PermFree tailB := by
  refine ⟨perm_free_append (li_free _ _) ?_, perm_free_append (perm_free_append (li_free _ _) ?_) ?_⟩
  · intro x hx; simp at hx; rcases hx with h | h <;> subst h <;> rfl
  · intro x hx; simp [restoreActs] at hx; rcases hx with h | h | h | h | h | h <;> subst h <;> rfl
  · intro x hx; simp [zeroRegActs] at hx; obtain ⟨r, _, h⟩ := hx; subst h; rfl

structure TailPre (o : Oracle) (input : CheckInput) (t : MachineState) : Prop where
  pc : t.pc = BitVec.ofNat 64 (4096+4*(464+2179))
  x16 : t.getReg .x16 = BitVec.ofNat 64 input.positions.card
  x29 : t.getReg .x29 = BitVec.ofNat 64 PB
  x24 : t.getReg .x24 = BitVec.ofNat 64 4096
  x25 : t.getReg .x25 = BitVec.ofNat 64 4294971392
  x26 : t.getReg .x26 = BitVec.ofNat 64 4294971424
  x27 : t.getReg .x27 = BitVec.ofNat 64 6375350304
  x28 : t.getReg .x28 = BitVec.ofNat 64 6509568096
  x2 : t.getReg .x2 = (start input).getReg .x2
  low : ∀ w < 2^33, (w < 2^25 ∨ 2^26 ≤ w) → w < proofWord → memoryView t w = memoryView (start input) w
  exp : ∀ w < 2^33, proofWord ≤ w → w < proofWord + 275*input.positions.card →
    memoryView t w = expW o input (w - proofWord)
  high : ∀ w < 2^33, proofWord + 275*input.positions.card ≤ w → memoryView t w = memoryView (start input) w

theorem past_proof (input : CheckInput) (u : Nat) (small : proofWord + u < 2^33) (past : input.proof.length ≤ 8*u) :
    memoryView (start input) (proofWord + u) = 0 := by
  show memoryView (loaderReference.initialState .check input) _ = _
  rw [proof_word loader_layout input u small]
  rw [Finset.sum_eq_zero (fun j _ => by rw [List.getElem?_eq_none (by omega)]; simp)]
  rfl

theorem zeroed_loader (k L : Nat) (r : Reg) (h : r ∈ zeroedRegs) : loaderReg k L r = 0 := by
  cases r <;> simp_all [zeroedRegs, loaderReg]

theorem tail_run (o : Oracle) (input : CheckInput) (pos : input.positions.card ≠ 0)
    (exact : input.proof.length = 720*input.positions.card+4224) (t : MachineState) (pre : TailPre o input t) :
    ∃ F cycles, Obs o packedImage t F 378 cycles 0 [] ∧ Quad.Checker.HeaderStart (expandInput o input) F ∧
      (∀ w < 2^33, (w < 2^25 ∨ 2^26 ≤ w) →
        memoryView F w = memoryView (loaderReference.initialState .check (expandInput o input)) w) := by
  have small := card_small input
  obtain ⟨cA, cZ, cAd1, cZ2, cB, cJ⟩ := tail_codes
  obtain ⟨freeA, freeB⟩ := tail_free input.positions.card
  -- part A
  obtain ⟨ok17, x17₁, keep17, view17⟩ := li_run o t .x17 2200 (by decide) (by decide)
  generalize ha : fixedOps o (liActs .x17 2200) t = a at ok17 x17₁ keep17 view17
  have a16 : a.getReg .x16 = BitVec.ofNat 64 input.positions.card := (keep17 _ (by decide)).trans pre.x16
  have a29 : a.getReg .x29 = BitVec.ofNat 64 PB := (keep17 _ (by decide)).trans pre.x29
  let a₂ := putReg (putReg a .x17 (BitVec.ofNat 64 (input.positions.card*2200))) .x6
    (BitVec.ofNat 64 (PB+input.positions.card*2200))
  have okA : validFixed o (tailA input.positions.card) t := by
    unfold tailA
    rw [validFixed_append, ha]
    refine ⟨ok17, ?_, ?_, trivial⟩
    · apply alu_mul; rw [a16, x17₁, word_mul _ _ (by omega) (by decide)]
    · apply alu_add
      simp only [fixedStep, put_reg_reg, ne_eq, reduceCtorEq, false_and, if_false, not_false_eq_true, and_self, if_true]
      rw [a29, word_add _ _ (by unfold PB; omega)]
  have aEq : fixedOps o (tailA input.positions.card) t = a₂ := by
    unfold tailA; rw [fixedOps_append, ha]; rfl
  have obsA := Obs.free o packedImage _ (464+2179) t pre.pc (wrap_fetch_ops image_wrap cA _ rfl) okA freeA
  rw [aEq] at obsA
  have pcA : a₂.pc = BitVec.ofNat 64 (4096+4*(464+2183)) := by
    rw [← aEq, fixed_ops_pc, pc_after _ _ _ pre.pc]; rfl
  -- clear the 343 words past the records, in two runs
  let B := proofWord+275*input.positions.card
  have a6 : a₂.getReg .x6 = BitVec.ofNat 64 (8*B) := by
    simp only [a₂, put_reg_reg, ne_eq, reduceCtorEq, not_false_eq_true, and_self, if_true]
    unfold B PB proofWord; congr 1; omega
  -- one run of `n` clears from word `D` starting at word index `W` of the wrapper, then optionally a bump
  have runZ : ∀ (W n D : Nat) (s : MachineState), WrapAt W (zeroStores .x6 n) → 8*n ≤ 2048 → D + n ≤ 2^33 →
      s.pc = BitVec.ofNat 64 (4096+4*(464+W)) → s.getReg .x6 = BitVec.ofNat 64 (8*D) →
      ∃ z cyc, Obs o packedImage s z n cyc 0 [] ∧ z.pc = BitVec.ofNat 64 (4096+4*(464+(W+n))) ∧
        (∀ r, z.getReg r = s.getReg r) ∧
        (∀ w < 2^33, memoryView z w = if D ≤ w ∧ w < D+n then 0 else memoryView s w) := by
    intro W n D s code room top pc x6
    obtain ⟨okZ, regsZ, memZ⟩ := zero_run o s .x6 D n x6 room top
    have obsZ := Obs.free o packedImage _ (464+W) s pc (wrap_fetch_ops image_wrap code _ (zero_acts_op _ _ _)) okZ
      (zero_free _ _ _)
    refine ⟨_, _, obsZ.cast (zero_acts_length _ _ _) rfl rfl rfl, ?_, regsZ, memZ⟩
    rw [fixed_ops_pc, pc_after _ _ _ pc, zero_acts_length]
    congr 1; omega
  have runB : ∀ (W D : Nat) (s : MachineState), wrapCode[W]? = some (.ADDI .x6 .x6 2040) → 8*D + 2040 < 2^64 →
      s.pc = BitVec.ofNat 64 (4096+4*(464+W)) → s.getReg .x6 = BitVec.ofNat 64 (8*D) →
      ∃ z cyc, Obs o packedImage s z 1 cyc 0 [] ∧ z.pc = BitVec.ofNat 64 (4096+4*(464+(W+1))) ∧
        z.getReg .x6 = BitVec.ofNat 64 (8*(D+255)) ∧ (∀ r, r ≠ .x6 → z.getReg r = s.getReg r) ∧
        memoryView z = memoryView s := by
    intro W D s code room pc x6
    let bump : List Action := [.offset .x6 .x6 2040 (BitVec.ofNat 64 (8*(D+255)))]
    have okBump : validFixed o bump s := by
      refine ⟨?_, trivial⟩
      show s.getReg .x6 + _ = _
      rw [x6, show (2040 : BitVec 12) = BitVec.ofNat 12 2040 from rfl, add_small _ 2040 (by decide) (by omega)]
      congr 1
    have obsBump := Obs.free o packedImage bump (464+W) s pc
      (wrap_fetch_ops image_wrap (show WrapAt W [.ADDI .x6 .x6 2040] from fun i hi => by
        have : i = 0 := by simpa using hi
        subst this; exact code) bump rfl) okBump (by intro x hx; simp [bump] at hx; subst hx; rfl)
    refine ⟨putReg s .x6 (BitVec.ofNat 64 (8*(D+255))), _, obsBump, ?_, ?_, ?_, ?_⟩
    · rw [← show fixedOps o bump s = putReg s .x6 (BitVec.ofNat 64 (8*(D+255))) from rfl, fixed_ops_pc, pc_after _ _ _ pc]
      congr 1
    · simp only [put_reg_reg, ne_eq, reduceCtorEq, not_false_eq_true, and_self, if_true]
    · intro r hr; rw [put_reg_reg, if_neg (fun h => hr h.1.symm)]
    · rw [put_reg_view]
  obtain ⟨z₁, c₁, obs₁, pc₁, reg₁, mem₁⟩ := runZ 2183 255 B a₂ cZ (by decide) (by unfold B proofWord; omega) pcA a6
  obtain ⟨y₁, d₁, obsY₁, pcY₁, x6Y₁, regY₁, memY₁⟩ := runB 2438 B z₁ cAd1 (by unfold B proofWord; omega) pc₁ (by rw [reg₁, a6])
  obtain ⟨z, c₂, obs₂, pcZ, reg₂, mem₂⟩ := runZ 2439 88 (B+255) y₁ cZ2 (by decide) (by unfold B proofWord; omega) pcY₁ x6Y₁
  have obsZ := obs₁.trans (obsY₁.trans obs₂)
  have zReg : ∀ x, x ≠ .x6 → z.getReg x = a₂.getReg x := by
    intro x hx
    rw [reg₂, regY₁ x hx, reg₁]
  have memZall : ∀ w < 2^33, memoryView z w = if B ≤ w ∧ w < B+343 then 0 else memoryView a₂ w := by
    intro w hw
    rw [mem₂ w hw, memY₁, mem₁ w hw]
    by_cases r1 : B ≤ w ∧ w < B+343
    · rw [if_pos r1]
      by_cases c : B+255 ≤ w ∧ w < B+255+88
      · rw [if_pos c]
      · rw [if_neg c, if_pos (by omega)]
    · rw [if_neg r1, if_neg (by omega), if_neg (by omega)]
  -- part B: x6, restore, zero
  obtain ⟨ok6, x6₁, keep6, view6⟩ := li_run o z .x6 2200 (by decide) (by decide)
  generalize hb : fixedOps o (liActs .x6 2200) z = b at ok6 x6₁ keep6 view6
  have bReg : ∀ x, x ≠ .x6 → b.getReg x = a₂.getReg x := fun x hx => by rw [keep6 x hx, zReg x hx]
  have bt : ∀ x, x ≠ .x6 → x ≠ .x17 → b.getReg x = t.getReg x := by
    intro x h6 h17
    rw [bReg x h6]; simp only [a₂]
    rw [put_reg_reg, if_neg (fun h => h6 h.1.symm), put_reg_reg, if_neg (fun h => h17 h.1.symm), keep17 x h17]
  let c := putReg (putReg (putReg (putReg (putReg (putReg b .x10 (BitVec.ofNat 64 4096)) .x11
    (BitVec.ofNat 64 4294971392)) .x12 (BitVec.ofNat 64 4294971424)) .x13 (BitVec.ofNat 64 6375350304)) .x14
    (BitVec.ofNat 64 6509568096)) .x15 (BitVec.ofNat 64 PB)
  have cEq : fixedOps o restoreActs b = c := rfl
  have okR : validFixed o restoreActs b := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;>
      simp only [fixedStep, Action.valid, put_reg_reg, ne_eq, reduceCtorEq, false_and, if_false] <;>
      rw [bt _ (by decide) (by decide)]
    · rw [pre.x24]; decide
    · rw [pre.x25]; decide
    · rw [pre.x26]; decide
    · rw [pre.x27]; decide
    · rw [pre.x28]; decide
    · rw [pre.x29]; unfold PB; decide
  obtain ⟨okZR, regsZR, viewZR⟩ := zero_regs_run o zeroedRegs c
  generalize hd : fixedOps o (zeroRegActs zeroedRegs) c = d at okZR regsZR viewZR
  have okB : validFixed o tailB z := by
    unfold tailB
    rw [validFixed_append, validFixed_append, fixedOps_append, hb, cEq]
    exact ⟨⟨ok6, okR⟩, okZR⟩
  have bEq : fixedOps o tailB z = d := by
    unfold tailB; rw [fixedOps_append, fixedOps_append, hb, cEq, hd]
  have obsB := Obs.free o packedImage _ (464+2527) z pcZ (wrap_fetch_ops image_wrap cB _
    (by unfold tailB; rw [List.map_append, List.map_append, li_acts_op, zero_regs_op]; rfl)) okB freeB
  rw [bEq] at obsB
  have pcD : d.pc = BitVec.ofNat 64 (4096+4*(464+2556)) := by
    rw [← bEq, fixed_ops_pc, pc_after _ _ _ pcZ]; rfl
  let F := execInstrBr d (.JAL .x0 2085076)
  have obsJ := Obs.step o packedImage d F _ (wrap_fetch image_wrap _ 2556 _ cJ pcD) (branch_step _ _ (Or.inr ⟨_, _, rfl⟩))
  have fReg : ∀ x, F.getReg x = d.getReg x := fun x => by
    show (execInstrBr d (.JAL .x0 2085076)).getReg x = _; rw [jal_exec, set_pc_reg]
  have fView : memoryView F = memoryView d := by
    show memoryView (execInstrBr d (.JAL .x0 2085076)) = _; rw [jal_exec, set_pc_view]
  have dView : memoryView d = memoryView z := by
    rw [viewZR]; simp only [c, put_reg_view]; rw [view6]
  refine ⟨F, _, (obsA.trans (obsZ.trans (obsB.trans obsJ))).cast (by simp [tailA, liActs,
    tailB, restoreActs, zeroRegActs, zeroedRegs]) rfl rfl rfl, ⟨?_, ?_, ?_⟩, ?_⟩
  · show (execInstrBr d (.JAL .x0 2085076)).pc = _
    rw [jal_exec]
    show d.pc + signExtend21 2085076 = _
    rw [pcD]; decide
  · rw [fReg, regsZR, if_neg (by decide)]
    simp only [c, put_reg_reg, ne_eq, reduceCtorEq, false_and, if_false]
    exact x6₁
  · intro r hr
    have target := loader_reg loader_layout (expandInput o input) r
    rw [target]
    have len : (expandInput o input).proof.length = 2200*input.positions.card := expand_proof_length _ _ _
    rw [len, show (expandInput o input).positions = input.positions from rfl, fReg, regsZR]
    by_cases zr : r ∈ zeroedRegs ∧ r ≠ .x0
    · rw [if_pos zr, zeroed_loader _ _ r zr.1]
    · rw [if_neg zr]
      cases r <;> simp_all [zeroedRegs, c, put_reg_reg, loaderReg]
      · rw [pre.x2, start_reg]; rfl
      · rfl
      · simp only [a₂, put_reg_reg, ne_eq, reduceCtorEq, false_and, if_false, not_false_eq_true, and_self, if_true]
        congr 1; ring
  · intro w hw out
    rw [fView, dView, memZall w hw, expanded_loader loader_layout o input w hw]
    have aview : memoryView a₂ w = memoryView t w := by simp only [a₂, put_reg_view]; rw [view17]
    by_cases zr : B ≤ w ∧ w < B+343
    · rw [if_pos zr, if_neg (by unfold B at zr; omega), if_neg (by unfold B at zr; omega)]
    · rw [if_neg zr, aview]
      by_cases lo : w < proofWord
      · rw [if_pos lo, pre.low w hw out lo]
      · rw [if_neg lo]
        by_cases mid : w < proofWord + 275*input.positions.card
        · rw [if_pos mid, pre.exp w hw (by omega) mid]
        · rw [if_neg mid, pre.high w hw (by omega)]
          obtain ⟨u, rfl⟩ : ∃ u, w = proofWord + u := ⟨w - proofWord, by omega⟩
          exact past_proof input u hw (by unfold B at zr; omega)

/-! ### The whole wrapper on an exact-length compact proof -/

theorem wrap_positive (o : Oracle) (input : CheckInput) (adm : input.proof.length < 2^64)
    (pos : input.positions.card ≠ 0) (exact : input.proof.length = 720*input.positions.card+4224) :
    ∃ F cycles rows, Obs o packedImage (start input) F (1684 + 872*input.positions.card) cycles 35 rows ∧
      Quad.Checker.HeaderStart (expandInput o input) F ∧
      (∀ w < 2^33, (w < 2^25 ∨ 2^26 ≤ w) →
        memoryView F w = memoryView (loaderReference.initialState .check (expandInput o input)) w) := by
  have small := card_small input
  obtain ⟨e, cE, obsE, done⟩ := wrap_entry o input adm pos exact
  have tab₀ : TableAt input e 0 e :=
    ⟨done.pc, by rw [done.x6]; rfl, by rw [done.x7], fun _ _ _ _ => rfl,
     fun w _ => by rw [if_neg (by omega), done.view]⟩
  obtain ⟨t₂₀, cT, obsT, tab₂₀⟩ := table_loop o input e e tab₀ 26 le_rfl
  obtain ⟨cHalf, obsHalf, tab⟩ := table_half o input e t₂₀ tab₂₀
  generalize ht : fixedOps o (thalfOps input.positions.card) t₂₀ = t at obsHalf tab
  obtain ⟨u, cH, rows, obsH, hinv, hbase, pcU⟩ := hash_phase o input e t tab
  -- registers carried from the entry
  have viaU : ∀ x, x ≠ .x5 → x ≠ .x10 → x ≠ .x11 → x ≠ .x12 → x ≠ .x13 → x ≠ .x6 → x ≠ .x7 → x ≠ .x31 →
      u.getReg x = e.getReg x := by
    intro x a b c d f g h i
    rw [hbase.keep x a b c d f, tab.keep x g h i]
  have regsU : SetupRegs input.positions.card u :=
    ⟨by rw [viaU _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        done.x16],
     by rw [viaU _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        done.x29],
     by rw [viaU _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        done.x27]; rfl⟩
  obtain ⟨okX, viewX, x8, x9, x18, x19, x20, x4, x30, x5, keepX⟩ :=
    exp_setup o input.positions.card (by omega) small u regsU
  have obsX := Obs.free o packedImage _ (464+1291) u pcU (wrap_fetch_ops image_wrap exp_codes _ (exp_acts_op _)) okX
    (exp_free _)
  generalize hv : fixedOps o (expActs input.positions.card) u = v at okX viewX x8 x9 x18 x19 x20 x4 x30 x5 keepX obsX
  have pcV : v.pc = BitVec.ofNat 64 (4096+4*(464+1307)) := by
    rw [← hv, fixed_ops_pc, pc_after _ _ _ pcU]; rfl
  have mem₀ : RecMem o input v input.positions.card v := by
    refine ⟨x8, x9, x18, x19, x20, x4, x30, x5, fun _ _ => rfl, ?_, ?_, ?_, ?_⟩
    · intro L h1 h2 j hj q hq
      rw [viewX]; exact hinv.slot L h1 (by omega) j hj q hq
    · intro w hw out _
      rw [viewX]; exact hinv.frame w hw (by unfold TEND; omega)
    · intro w _ lo hi; omega
    · intro w hw hi
      rw [viewX]; exact hinv.frame w hw (Or.inr (by unfold TEND proofWord at *; omega))
  obtain ⟨T, cR, obsR, memT, pcT⟩ := rec_loop o input v v mem₀ pcV pos input.positions.card le_rfl
  simp only [Nat.sub_self, if_true] at memT pcT
  have viaT : ∀ x, RecKept x → ¬ ExpTouched x → x ≠ .x5 → x ≠ .x10 → x ≠ .x11 → x ≠ .x12 → x ≠ .x13 → x ≠ .x6 →
      x ≠ .x7 → x ≠ .x31 → T.getReg x = e.getReg x := by
    intro x rk nt a b c d f g h i
    rw [memT.keep x rk, keepX x nt, viaU x a b c d f g h i]
  have pre : TailPre o input T := by
    refine ⟨pcT, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals first
      | (intro w hw out lo; have := memT.low w hw out (by omega); exact this)
      | (intro w hw lo hi; exact memT.exp w hw (by omega) hi)
      | (intro w hw hi; exact memT.high w hw hi)
      | skip
    · rw [viaT _ (by decide) (by unfold ExpTouched; decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide), done.x16]
    · rw [viaT _ (by decide) (by unfold ExpTouched; decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide), done.x29]
    · rw [viaT _ (by decide) (by unfold ExpTouched; decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide), done.x24]
    · rw [viaT _ (by decide) (by unfold ExpTouched; decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide), done.x25]
    · rw [viaT _ (by decide) (by unfold ExpTouched; decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide), done.x26]
    · rw [viaT _ (by decide) (by unfold ExpTouched; decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide), done.x27]
    · rw [viaT _ (by decide) (by unfold ExpTouched; decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide), done.x28]
    · rw [viaT _ (by decide) (by unfold ExpTouched; decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide), done.x2]
  obtain ⟨F, cF, obsF, header, frame⟩ := tail_run o input pos exact T pre
  have len : (expActs input.positions.card).length = 16 := rfl
  exact ⟨F, _, _, (obsE.trans (obsT.trans (obsHalf.trans (obsH.trans (obsX.trans (obsR.trans obsF)))))).cast
    (by rw [len]; ring) rfl (by simp) rfl, header, frame⟩

end TwoPermutationPrototype.HybWrap
