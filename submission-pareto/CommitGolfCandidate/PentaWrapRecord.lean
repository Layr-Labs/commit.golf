import CommitGolfCandidate.PentaWrapTable

/-! One record of the checker wrapper (wrapper offsets 115-287): copy the 114 prefix doublewords
of compressed record `r` to expanded record `r` from the top down, then fill its four top blocks
(levels 7-10) from the doubled table, move the three pointers to record `r - 1`, and loop while
`r ≥ 1`. Records are processed from the last one down, so the compressed prefixes still to be
read always lie below everything written so far. The central fact is `fill_pair` / `level_fill`:
the top block of level `7 + lvl` of record `r` is read from the table at the group and rotation of
the record's index. -/

namespace TwoPermutationPrototype.PentaWrap
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.RV64 (memoryView wordAddress)

set_option maxRecDepth 100000

/-- The wrapper's constants (offsets 94-105). -/
structure Consts (state : MachineState) : Prop where
  q7 : state.getReg .x8 = BitVec.ofNat 64 78125
  five : state.getReg .x9 = BitVec.ofNat 64 5
  width : state.getReg .x18 = BitVec.ofNat 64 320
  b0 : state.getReg .x19 = BitVec.ofNat 64 (TABLE + 320*capFirst 0 + 32)
  b1 : state.getReg .x20 = BitVec.ofNat 64 (TABLE + 320*capFirst 1 + 32)
  b2 : state.getReg .x21 = BitVec.ofNat 64 (TABLE + 320*capFirst 2 + 32)
  b3 : state.getReg .x22 = BitVec.ofNat 64 (TABLE + 320*capFirst 3 + 32)

theorem Consts.base {state : MachineState} (c : Consts state) (lvl : Nat) (hl : lvl < 4) :
    state.getReg (levelBase lvl) = BitVec.ofNat 64 (TABLE + 320*capFirst lvl + 32) := by
  interval_cases lvl
  · exact c.b0
  · exact c.b1
  · exact c.b2
  · exact c.b3

def constRegs : List Reg := [.x8, .x9, .x18, .x19, .x20, .x21, .x22]

theorem Consts.keep {a b : MachineState} (c : Consts a) (same : ∀ r ∈ constRegs, b.getReg r = a.getReg r) :
    Consts b :=
  ⟨(same .x8 (by decide)).trans c.q7, (same .x9 (by decide)).trans c.five, (same .x18 (by decide)).trans c.width,
   (same .x19 (by decide)).trans c.b0, (same .x20 (by decide)).trans c.b1, (same .x21 (by decide)).trans c.b2,
   (same .x22 (by decide)).trans c.b3⟩

theorem Kept.keep {init a b : MachineState} (c : Kept init a) (same : ∀ r ∈ keptRegs, b.getReg r = a.getReg r) :
    Kept init b := fun r member => (same r member).trans (c r member)

/-! ### Arithmetic -/

theorem divu_value (a b : Nat) (hb : 0 < b) (ha : a < 2^64) (hb' : b < 2^64) :
    rv64_divu (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = BitVec.ofNat 64 (a / b) := by
  unfold rv64_divu
  have nonzero : BitVec.ofNat 64 b ≠ 0#64 := by
    intro same
    have := congrArg BitVec.toNat same
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb'] at this
    omega
  rw [if_neg (by simpa using nonzero)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_udiv]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb']
  rw [Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) ha)]

theorem cap_quot_succ (i lvl : Nat) : capQuot i (lvl+1) = capQuot i lvl / 5 := by
  unfold capQuot
  rw [show 7 + (lvl+1) = (7+lvl)+1 by omega, pow_succ, Nat.div_div_eq_div_mul]

theorem cap_quot_zero (i : Nat) : capQuot i 0 = i / 78125 := by
  unfold capQuot; norm_num

theorem cap_quot_small (i lvl : Nat) (hi : i < 16777216) : capQuot i lvl < 16777216 := by
  unfold capQuot
  exact lt_of_le_of_lt (Nat.div_le_self _ _) hi

/-- Every level-`(7 + lvl)` group lies in the table: `capFirst lvl + group ≤ 54`. -/
theorem quot_bound (i lvl : Nat) (hi : i < 16777216) (hl : lvl < 4) :
    capFirst lvl + capQuot i lvl / 5 ≤ 54 := by
  rw [← cap_quot_succ]
  unfold capQuot capFirst
  interval_cases lvl <;> norm_num <;> omega

/-! ### The level fill -/

theorem fill_offsets : ∀ lvl < 4, ∀ m < 16,
    signExtend12 (BitVec.ofNat 12 (8*m)) = BitVec.ofNat 64 (8*m) ∧
    signExtend12 (BitVec.ofNat 12 (912+128*lvl+8*m)) = BitVec.ofNat 64 (912+128*lvl+8*m) := by
  decide

theorem fill_code : ∀ lvl < 4,
    WrapAt (124+40*lvl) [.DIVU .x7 .x6 .x9, .MUL .x28 .x7 .x9, .SUB .x28 .x6 .x28, .MUL .x29 .x7 .x18,
      .SLLI .x28 .x28 5, .ADD .x29 .x29 .x28, .ADD .x29 .x29 (levelBase lvl)] ∧
    (∀ m < 16, wrapCode[124+40*lvl+7+2*m]? = some (.LD .x31 .x29 (BitVec.ofNat 12 (8*m))) ∧
      wrapCode[124+40*lvl+7+2*m+1]? = some (.SD .x25 .x31 (BitVec.ofNat 12 (912+128*lvl+8*m)))) ∧
    WrapAt (124+40*lvl+39) [.ADDI .x6 .x7 0] := by
  decide +kernel


/-- Filling the top blocks of record `r`: levels below `7 + lvl` are done; `x6` is the record's
level-`(7 + lvl)` quotient. -/
structure Filling (sub : Submission) (input : CheckInput) (r lvl : Nat) (state : MachineState) : Prop where
  x24 : state.getReg .x24 = BitVec.ofNat 64 (PENTA_PROOF_BASE + 912*r)
  x25 : state.getReg .x25 = BitVec.ofNat 64 (PENTA_PROOF_BASE + 1424*r)
  x26 : state.getReg .x26 = BitVec.ofNat 64 (6375350304 + 8*r)
  x6 : state.getReg .x6 = BitVec.ofNat 64 (capQuot (sortedIndex input.positions r) lvl)
  consts : Consts state
  kept : Kept (sub.initialState .check input) state
  table : ∀ x < 2200, memoryView state (TBW + x) = tableWord sub input x
  low : ∀ w < proofWord + 114*r, (w < TBW ∨ TBW + 2200 ≤ w) →
    memoryView state w = memoryView (sub.initialState .check input) w
  filled : ∀ w, proofWord + 178*r ≤ w → w < proofWord + 178*r + 114 + 16*lvl →
    memoryView state w = expandedWord sub input (w - proofWord)
  done : ∀ w, proofWord + 178*(r+1) ≤ w → w < proofWord + 178*input.positions.card →
    memoryView state w = expandedWord sub input (w - proofWord)
  high : ∀ w < 2^33, proofWord + 178*input.positions.card ≤ w → memoryView state w = 0

theorem level_base_ne (lvl : Nat) : levelBase lvl ≠ .x7 ∧ levelBase lvl ≠ .x28 ∧ levelBase lvl ≠ .x29 := by
  unfold levelBase; split <;> decide

def fillHead (lvl : Nat) : List Instr :=
  [.DIVU .x7 .x6 .x9, .MUL .x28 .x7 .x9, .SUB .x28 .x6 .x28, .MUL .x29 .x7 .x18,
   .SLLI .x28 .x28 5, .ADD .x29 .x29 .x28, .ADD .x29 .x29 (levelBase lvl)]

/-- The address computation of a level fill. -/
theorem fill_head_regs (state : MachineState) (lvl q cf : Nat) (hq : q < 16777216) (hcf : cf ≤ 54)
    (x6 : state.getReg .x6 = BitVec.ofNat 64 q) (x9 : state.getReg .x9 = BitVec.ofNat 64 5)
    (x18 : state.getReg .x18 = BitVec.ofNat 64 320)
    (base : state.getReg (levelBase lvl) = BitVec.ofNat 64 (TABLE + 320*cf + 32)) :
    ((fillHead lvl).foldl execInstrBr state).getReg .x7 = BitVec.ofNat 64 (q/5) ∧
    ((fillHead lvl).foldl execInstrBr state).getReg .x29 = wordAddress (TBW + 40*(cf + q/5) + 4*(q%5 + 1)) ∧
    ∀ r, r ≠ .x7 → r ≠ .x28 → r ≠ .x29 → ((fillHead lvl).foldl execInstrBr state).getReg r = state.getReg r := by
  obtain ⟨n7, n28, n29⟩ := level_base_ne lvl
  have tb : TABLE = 268435456 := rfl
  have tw : TBW = 33554432 := rfl
  have quot : rv64_divu (BitVec.ofNat 64 q) (BitVec.ofNat 64 5) = BitVec.ofNat 64 (q/5) :=
    divu_value q 5 (by decide) (by omega) (by decide)
  refine ⟨?_, ?_, ?_⟩
  · simp [fillHead, execInstrBr, get_reg_set_reg, x6, x9, quot]
  · simp only [fillHead, List.foldl_cons, List.foldl_nil, execInstrBr, MachineState.getReg_setPC, get_reg_set_reg]
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, and_true, and_false, if_true, if_false, Ne.symm n29,
      Ne.symm n28, Ne.symm n7, true_and, false_and, n29, n28, n7]
    rw [x6, x9, x18, base, quot]
    unfold wordAddress
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq]
    have hmod : q / 5 * 5 % 18446744073709551616 = q / 5 * 5 := Nat.mod_eq_of_lt (by omega)
    norm_num
    omega
  · intro r a b c
    simp [fillHead, execInstrBr, get_reg_set_reg, Ne.symm a, Ne.symm b, Ne.symm c]

/-- Part of the level fill after `m` of the 16 pairs. -/
structure Pairs (sub : Submission) (input : CheckInput) (r lvl m : Nat) (state : MachineState) : Prop where
  x24 : state.getReg .x24 = BitVec.ofNat 64 (PENTA_PROOF_BASE + 912*r)
  x25 : state.getReg .x25 = BitVec.ofNat 64 (PENTA_PROOF_BASE + 1424*r)
  x26 : state.getReg .x26 = BitVec.ofNat 64 (6375350304 + 8*r)
  x7 : state.getReg .x7 = BitVec.ofNat 64 (capQuot (sortedIndex input.positions r) lvl / 5)
  x29 : state.getReg .x29 = wordAddress (TBW + 40*(capFirst lvl + capQuot (sortedIndex input.positions r) lvl / 5) +
    4*(capQuot (sortedIndex input.positions r) lvl % 5 + 1))
  consts : Consts state
  kept : Kept (sub.initialState .check input) state
  table : ∀ x < 2200, memoryView state (TBW + x) = tableWord sub input x
  low : ∀ w < proofWord + 114*r, (w < TBW ∨ TBW + 2200 ≤ w) →
    memoryView state w = memoryView (sub.initialState .check input) w
  filled : ∀ w, proofWord + 178*r ≤ w → w < proofWord + 178*r + 114 + 16*lvl + m →
    memoryView state w = expandedWord sub input (w - proofWord)
  done : ∀ w, proofWord + 178*(r+1) ≤ w → w < proofWord + 178*input.positions.card →
    memoryView state w = expandedWord sub input (w - proofWord)
  high : ∀ w < 2^33, proofWord + 178*input.positions.card ≤ w → memoryView state w = 0

/-- One table read and expanded-record write of the level fill. -/
theorem fill_pair {sub : Submission} (wrap : WrapImage (sub.image .check)) (input : CheckInput)
    (r lvl m : Nat) (present : r < input.positions.card) (hl : lvl < 4) (hm : m < 16)
    (state : MachineState) (pc : state.pc = BitVec.ofNat 64 (4096+4*(460+(124+40*lvl+7+2*m))))
    (at_ : Pairs sub input r lvl m state) :
    ∃ next : MachineState, Hop (sub.image .check) state next 2 2 ∧ Pairs sub input r lvl (m+1) next ∧
      next.pc = BitVec.ofNat 64 (4096+4*(460+(124+40*lvl+7+2*(m+1)))) := by
  have card : input.positions.card ≤ 16777216 := by
    have : input.positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
    exact this
  have pw : proofWord = 1350566924 := rfl
  have pb : PENTA_PROOF_BASE = 10804535392 := rfl
  have tw : TBW = 33554432 := rfl
  have room : MEMORY_BYTES = 68719476736 := rfl
  obtain ⟨_, pairs, _⟩ := fill_code lvl hl
  obtain ⟨c₁, c₂⟩ := pairs m hm
  obtain ⟨o₁, o₂⟩ := fill_offsets lvl hl m hm
  have bound := quot_bound (sortedIndex input.positions r) lvl (sorted_index_small _ _) hl
  generalize hq : capQuot (sortedIndex input.positions r) lvl = q at bound
  have rot : q % 5 < 5 := Nat.mod_lt _ (by decide)
  have x29 : state.getReg .x29 = wordAddress (TBW + 40*(capFirst lvl + q/5) + 4*(q%5 + 1)) := by
    rw [at_.x29, hq]
  let x := 40*(capFirst lvl + q/5) + 4*(q%5 + 1) + m
  have hx : x < 2200 := by simp only [x]; omega
  -- load the table word
  obtain ⟨run₁, pc₁, mem₁, x31₁, keep₁⟩ := wrap_load wrap state .x31 .x29 _ (124+40*lvl+7+2*m) c₁ pc
    (8*(TBW + x)) (by rw [x29, o₁]; unfold wordAddress; rw [← BitVec.ofNat_add]; congr 1; simp only [x]; omega)
    (by omega) (by omega)
  generalize h₁ : execInstrBr state (.LD .x31 .x29 (BitVec.ofNat 12 (8*m))) = s₁ at run₁ pc₁ mem₁ x31₁ keep₁
  have value : s₁.getReg .x31 = expandedWord sub input (178*r + 114 + 16*lvl + m) := by
    rw [x31₁, if_neg (by decide)]
    have e : state.getMem (BitVec.ofNat 64 (8*(TBW + x))) = memoryView state (TBW + x) := rfl
    rw [e, at_.table x hx]
    unfold tableWord expandedWord
    have v₁ : (178*r + 114 + 16*lvl + m) % 178 = 114 + 16*lvl + m := by omega
    have v₂ : (178*r + 114 + 16*lvl + m) / 178 = r := by omega
    rw [v₁, v₂, if_neg (by omega)]
    dsimp only
    rw [show (114 + 16*lvl + m - 114)/16 = lvl by omega,
      show (114 + 16*lvl + m - 114) % 16 = m by omega, hq, show x / 40 = capFirst lvl + q/5 by simp only [x]; omega,
      show x % 40 % 20 = (4*(q%5+1) + m) % 20 by simp only [x]; omega]
  -- store into the expanded record
  let dest := proofWord + 178*r + 114 + 16*lvl + m
  obtain ⟨run₂, pc₂, view₂, keep₂⟩ := wrap_store wrap s₁ .x25 .x31 _ (124+40*lvl+7+2*m+1) c₂ pc₁ dest
    (by rw [keep₁ .x25 (by decide), at_.x25, o₂, ← BitVec.ofNat_add]; apply word_of_bytes; simp only [dest]; omega)
    (by simp only [dest]; omega)
  generalize h₂ : execInstrBr s₁ (.SD .x25 .x31 (BitVec.ofNat 12 (912+128*lvl+8*m))) = s₂ at run₂ pc₂ view₂ keep₂
  have regs (reg : Reg) (a : reg ≠ .x31) : s₂.getReg reg = state.getReg reg := by rw [keep₂, keep₁ reg a]
  have keptNe : ∀ reg ∈ keptRegs, reg ≠ .x31 := by decide
  have constNe : ∀ reg ∈ constRegs, reg ≠ .x31 := by decide
  refine ⟨s₂, (run₁.trans run₂).cast rfl rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [regs .x24 (by decide), at_.x24]
  · rw [regs .x25 (by decide), at_.x25]
  · rw [regs .x26 (by decide), at_.x26]
  · rw [regs .x7 (by decide), at_.x7]
  · rw [regs .x29 (by decide), at_.x29]
  · exact at_.consts.keep (fun reg member => regs reg (constNe reg member))
  · exact at_.kept.keep (fun reg member => regs reg (keptNe reg member))
  · intro y hy
    rw [view₂ _ (by omega), if_neg (by simp only [dest]; omega), view_of_mem mem₁]
    exact at_.table y hy
  · intro w hw side
    rw [view₂ _ (by omega), if_neg (by simp only [dest]; omega), view_of_mem mem₁]
    exact at_.low w hw side
  · intro w lo hi
    have hw : w < 2^61 := by omega
    rw [view₂ _ hw]
    by_cases here : w = dest
    · have index : w - proofWord = 178*r + 114 + 16*lvl + m := by simp only [dest] at here; omega
      rw [if_pos here, value, index]
    · rw [if_neg here, view_of_mem mem₁]
      exact at_.filled w lo (by simp only [dest] at here; omega)
  · intro w lo hi
    rw [view₂ _ (by omega), if_neg (by simp only [dest]; omega), view_of_mem mem₁]
    exact at_.done w lo hi
  · intro w hw lo
    rw [view₂ _ (by omega), if_neg (by simp only [dest]; omega), view_of_mem mem₁]
    exact at_.high w hw lo
  · rw [pc₂]
    congr 1


theorem fill_pairs {sub : Submission} (wrap : WrapImage (sub.image .check)) (input : CheckInput)
    (r lvl : Nat) (present : r < input.positions.card) (hl : lvl < 4) :
    ∀ m ≤ 16, ∀ state : MachineState, state.pc = BitVec.ofNat 64 (4096+4*(460+(124+40*lvl+7+2*0))) →
      Pairs sub input r lvl 0 state →
      ∃ next : MachineState, Hop (sub.image .check) state next (2*m) (2*m) ∧ Pairs sub input r lvl m next ∧
        next.pc = BitVec.ofNat 64 (4096+4*(460+(124+40*lvl+7+2*m))) := by
  intro m
  induction m with
  | zero => intro _ state pc at_; exact ⟨state, Hop.zero _ _, at_, pc⟩
  | succ m ih =>
    intro le state pc at_
    obtain ⟨mid, run, atMid, pcMid⟩ := ih (by omega) state pc at_
    obtain ⟨next, run₂, atNext, pcNext⟩ := fill_pair wrap input r lvl m present hl (by omega) mid pcMid atMid
    exact ⟨next, (run.trans run₂).cast (by omega) (by omega), atNext, pcNext⟩

/-- The top block of level `7 + lvl` of record `r`, read from the doubled table. -/
theorem level_fill {sub : Submission} (wrap : WrapImage (sub.image .check)) (input : CheckInput)
    (r lvl : Nat) (present : r < input.positions.card) (hl : lvl < 4)
    (state : MachineState) (pc : state.pc = BitVec.ofNat 64 (4096+4*(460+(124+40*lvl))))
    (at_ : Filling sub input r lvl state) :
    ∃ next : MachineState, Hop (sub.image .check) state next 40 49 ∧ Filling sub input r (lvl+1) next ∧
      next.pc = BitVec.ofNat 64 (4096+4*(460+(124+40*(lvl+1)))) := by
  obtain ⟨c₁, _, c₃⟩ := fill_code lvl hl
  have pure₁ : (fillHead lvl).all wrapPure = true := by unfold fillHead; simp [wrapPure]
  have run₁ := wrap_pure_run wrap (fillHead lvl) (124+40*lvl) state c₁ pc pure₁
  have pc₁ := wrap_pure_pc (fillHead lvl) state pure₁
  have mem₁ := wrap_pure_mem (fillHead lvl) state pure₁
  have q := sorted_index_small input.positions r
  obtain ⟨x7₁, x29₁, keep₁⟩ := fill_head_regs state lvl (capQuot (sortedIndex input.positions r) lvl) (capFirst lvl)
    (cap_quot_small _ _ q) (by unfold capFirst; split <;> omega) at_.x6 at_.consts.five at_.consts.width
    (at_.consts.base lvl hl)
  generalize h₁ : (fillHead lvl).foldl execInstrBr state = s₁ at run₁ pc₁ mem₁ x7₁ x29₁ keep₁
  have keptNe : ∀ reg ∈ keptRegs, reg ≠ .x7 ∧ reg ≠ .x28 ∧ reg ≠ .x29 := by decide
  have constNe : ∀ reg ∈ constRegs, reg ≠ .x7 ∧ reg ≠ .x28 ∧ reg ≠ .x29 := by decide
  have pairs₀ : Pairs sub input r lvl 0 s₁ := by
    refine ⟨?_, ?_, ?_, x7₁, x29₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [keep₁ .x24 (by decide) (by decide) (by decide), at_.x24]
    · rw [keep₁ .x25 (by decide) (by decide) (by decide), at_.x25]
    · rw [keep₁ .x26 (by decide) (by decide) (by decide), at_.x26]
    · exact at_.consts.keep (fun reg member => by
        obtain ⟨a, b, c⟩ := constNe reg member; exact keep₁ reg a b c)
    · exact at_.kept.keep (fun reg member => by
        obtain ⟨a, b, c⟩ := keptNe reg member; exact keep₁ reg a b c)
    · intro x hx; rw [view_of_mem mem₁]; exact at_.table x hx
    · intro w hw side; rw [view_of_mem mem₁]; exact at_.low w hw side
    · intro w lo hi; rw [view_of_mem mem₁]; exact at_.filled w lo (by omega)
    · intro w lo hi; rw [view_of_mem mem₁]; exact at_.done w lo hi
    · intro w hw lo; rw [view_of_mem mem₁]; exact at_.high w hw lo
  have pcPairs : s₁.pc = BitVec.ofNat 64 (4096+4*(460+(124+40*lvl+7+2*0))) := by
    rw [pc₁, pc, pc_add]
    unfold fillHead
    rfl
  obtain ⟨s₂, run₂, at₂, pc₂⟩ := fill_pairs wrap input r lvl present hl 16 le_rfl s₁ pcPairs pairs₀
  have pure₃ : ([.ADDI .x6 .x7 0] : List Instr).all wrapPure = true := rfl
  have run₃ := wrap_pure_run wrap _ (124+40*lvl+39) s₂ c₃ (by rw [pc₂]) pure₃
  have pc₃ := wrap_pure_pc _ s₂ pure₃
  have mem₃ := wrap_pure_mem _ s₂ pure₃
  have x6₃ : (([.ADDI .x6 .x7 0] : List Instr).foldl execInstrBr s₂).getReg .x6 = s₂.getReg .x7 + signExtend12 0 := by
    simp [execInstrBr, get_reg_set_reg]
  have keep₃ (reg : Reg) (a : reg ≠ .x6) :
      (([.ADDI .x6 .x7 0] : List Instr).foldl execInstrBr s₂).getReg reg = s₂.getReg reg := by
    simp [execInstrBr, get_reg_set_reg, Ne.symm a]
  generalize h₃ : ([.ADDI .x6 .x7 0] : List Instr).foldl execInstrBr s₂ = s₃ at run₃ pc₃ mem₃ x6₃ keep₃
  have keptNe6 : ∀ reg ∈ keptRegs, reg ≠ .x6 := by decide
  have constNe6 : ∀ reg ∈ constRegs, reg ≠ .x6 := by decide
  refine ⟨s₃, ((run₁.trans run₂).trans run₃).cast (by unfold fillHead; simp) (by unfold fillHead; simp [wrapCost,
      instructionCycles]), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [keep₃ .x24 (by decide), at₂.x24]
  · rw [keep₃ .x25 (by decide), at₂.x25]
  · rw [keep₃ .x26 (by decide), at₂.x26]
  · rw [x6₃, at₂.x7, show signExtend12 (0 : BitVec 12) = 0#64 by decide, BitVec.add_zero, cap_quot_succ]
  · exact at₂.consts.keep (fun reg member => keep₃ reg (constNe6 reg member))
  · exact at₂.kept.keep (fun reg member => keep₃ reg (keptNe6 reg member))
  · intro x hx; rw [view_of_mem mem₃]; exact at₂.table x hx
  · intro w hw side; rw [view_of_mem mem₃]; exact at₂.low w hw side
  · intro w lo hi; rw [view_of_mem mem₃]; exact at₂.filled w lo (by omega)
  · intro w lo hi; rw [view_of_mem mem₃]; exact at₂.done w lo hi
  · intro w hw lo; rw [view_of_mem mem₃]; exact at₂.high w hw lo
  · rw [pc₃, pc₂, pc_add]
    congr 1


/-! ### The prefix copy -/

/-- Records `r … k-1` are expanded; the pointers name record `r - 1`. -/
structure Expanding (sub : Submission) (input : CheckInput) (r : Nat) (state : MachineState) : Prop where
  x24 : state.getReg .x24 = BitVec.ofNat 64 (PENTA_PROOF_BASE + 912*r - 912)
  x25 : state.getReg .x25 = BitVec.ofNat 64 (PENTA_PROOF_BASE + 1424*r - 1424)
  x26 : state.getReg .x26 = BitVec.ofNat 64 (6375350304 + 8*r - 8)
  consts : Consts state
  kept : Kept (sub.initialState .check input) state
  table : ∀ x < 2200, memoryView state (TBW + x) = tableWord sub input x
  low : ∀ w < proofWord + 114*r, (w < TBW ∨ TBW + 2200 ≤ w) →
    memoryView state w = memoryView (sub.initialState .check input) w
  done : ∀ w, proofWord + 178*r ≤ w → w < proofWord + 178*input.positions.card →
    memoryView state w = expandedWord sub input (w - proofWord)
  high : ∀ w < 2^33, proofWord + 178*input.positions.card ≤ w → memoryView state w = 0

/-- Copying record `r`: `n` prefix doublewords are still to be copied. -/
structure Copying (sub : Submission) (input : CheckInput) (r n : Nat) (state : MachineState) : Prop where
  x24 : state.getReg .x24 = BitVec.ofNat 64 (PENTA_PROOF_BASE + 912*r)
  x25 : state.getReg .x25 = BitVec.ofNat 64 (PENTA_PROOF_BASE + 1424*r)
  x26 : state.getReg .x26 = BitVec.ofNat 64 (6375350304 + 8*r)
  consts : Consts state
  kept : Kept (sub.initialState .check input) state
  table : ∀ x < 2200, memoryView state (TBW + x) = tableWord sub input x
  low : ∀ w < proofWord + 114*r + n, (w < TBW ∨ TBW + 2200 ≤ w) →
    memoryView state w = memoryView (sub.initialState .check input) w
  copied : ∀ w, proofWord + 178*r + n ≤ w → w < proofWord + 178*r + 114 →
    memoryView state w = expandedWord sub input (w - proofWord)
  done : ∀ w, proofWord + 178*(r+1) ≤ w → w < proofWord + 178*input.positions.card →
    memoryView state w = expandedWord sub input (w - proofWord)
  high : ∀ w < 2^33, proofWord + 178*input.positions.card ≤ w → memoryView state w = 0

theorem copy_code : WrapAt 116 [.ADD .x5 .x24 .x27] ∧ wrapCode[117]? = some (.LD .x5 .x5 0) ∧
    WrapAt 118 [.ADD .x6 .x25 .x27] ∧ wrapCode[119]? = some (.SD .x6 .x5 0) ∧
    WrapAt 120 [.ADDI .x27 .x27 4088] ∧ wrapCode[121]? = some (.BGE .x27 .x0 8172) := by
  decide +kernel

theorem copy_offset_small (d : Nat) (h : d < 114) : BitVec.slt (BitVec.ofNat 64 (8*d)) 0#64 = false := by
  rw [BitVec.slt_eq_decide, BitVec.toInt_eq_toNat_cond]
  have small : (BitVec.ofNat 64 (8*d)).toNat = 8*d := by rw [BitVec.toNat_ofNat]; omega
  rw [small]
  simp
  omega

theorem copy_offset_done : BitVec.slt (BitVec.ofNat 64 (2^64-8)) 0#64 = true := by decide

theorem neg_imm (a c : Nat) (imm : BitVec 12) (h : c ≤ a) (small : a < 2^64)
    (himm : signExtend12 imm = BitVec.ofNat 64 (2^64 - c)) :
    BitVec.ofNat 64 a + signExtend12 imm = BitVec.ofNat 64 (a - c) := by
  rw [himm, ← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega

/-- One iteration of the prefix copy, copying doubleword `n - 1`. -/
theorem copy_step {sub : Submission} (wrap : WrapImage (sub.image .check))
    (input : CheckInput) (r n : Nat) (present : r < input.positions.card) (live : 1 ≤ n) (small : n ≤ 114)
    (state : MachineState) (pc : state.pc = BitVec.ofNat 64 (4096+4*(460+116)))
    (counter : state.getReg .x27 = BitVec.ofNat 64 (8*(n-1)))
    (at_ : Copying sub input r n state) :
    ∃ next : MachineState, Hop (sub.image .check) state next 6 6 ∧ Copying sub input r (n-1) next ∧
      next.pc = BitVec.ofNat 64 (4096+4*(460+(if n = 1 then 122 else 116))) ∧
      (n ≠ 1 → next.getReg .x27 = BitVec.ofNat 64 (8*(n-2))) := by
  have card : input.positions.card ≤ 16777216 := by
    have : input.positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
    exact this
  obtain ⟨c₁, c₂, c₃, c₄, c₅, c₆⟩ := copy_code
  have pw : proofWord = 1350566924 := rfl
  have pb : PENTA_PROOF_BASE = 10804535392 := rfl
  have tw : TBW = 33554432 := rfl
  have room : MEMORY_BYTES = 68719476736 := rfl
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at counter ⊢
  -- source address
  have pure₁ : ([.ADD .x5 .x24 .x27] : List Instr).all wrapPure = true := rfl
  have run₁ := wrap_pure_run wrap _ 116 state c₁ pc pure₁
  have pc₁ := wrap_pure_pc _ state pure₁
  have mem₁ := wrap_pure_mem _ state pure₁
  have x5₁ : (([.ADD .x5 .x24 .x27] : List Instr).foldl execInstrBr state).getReg .x5 =
      state.getReg .x24 + state.getReg .x27 := by simp [execInstrBr, get_reg_set_reg]
  have keep₁ (reg : Reg) (a : reg ≠ .x5) :
      (([.ADD .x5 .x24 .x27] : List Instr).foldl execInstrBr state).getReg reg = state.getReg reg := by
    simp [execInstrBr, get_reg_set_reg, Ne.symm a]
  generalize h₁ : ([.ADD .x5 .x24 .x27] : List Instr).foldl execInstrBr state = s₁ at run₁ pc₁ mem₁ x5₁ keep₁
  -- load
  obtain ⟨run₂, pc₂, mem₂, x5₂, keep₂⟩ := wrap_load wrap s₁ .x5 .x5 0 117 c₂ (by rw [pc₁, pc, pc_add]; rfl)
    (8*(proofWord + 114*r + d))
    (by rw [x5₁, at_.x24, counter, show signExtend12 (0 : BitVec 12) = 0#64 by decide, BitVec.add_zero,
          ← BitVec.ofNat_add]; congr 1; omega)
    (by omega) (by omega)
  generalize h₂ : execInstrBr s₁ (.LD .x5 .x5 0) = s₂ at run₂ pc₂ mem₂ x5₂ keep₂
  have loaded : s₂.getReg .x5 = expandedWord sub input (178*r + d) := by
    rw [x5₂, if_neg (by decide)]
    have e : s₁.getMem (BitVec.ofNat 64 (8*(proofWord + 114*r + d))) = memoryView state (proofWord + 114*r + d) := by
      rw [show s₁.getMem (BitVec.ofNat 64 (8*(proofWord + 114*r + d))) = memoryView s₁ (proofWord + 114*r + d) from rfl,
        view_of_mem mem₁]
    rw [e, at_.low _ (by omega) (by right; omega)]
    unfold expandedWord sourceWord
    rw [if_pos (by omega), show (178*r+d)/178 = r by omega, show (178*r+d)%178 = d by omega,
      show proofWord + 114*r + d = proofWord + (114*r + d) by omega]
  -- destination address
  have pure₃ : ([.ADD .x6 .x25 .x27] : List Instr).all wrapPure = true := rfl
  have run₃ := wrap_pure_run wrap _ 118 s₂ c₃ (by rw [pc₂]) pure₃
  have pc₃ := wrap_pure_pc _ s₂ pure₃
  have mem₃ := wrap_pure_mem _ s₂ pure₃
  have x6₃ : (([.ADD .x6 .x25 .x27] : List Instr).foldl execInstrBr s₂).getReg .x6 =
      s₂.getReg .x25 + s₂.getReg .x27 := by simp [execInstrBr, get_reg_set_reg]
  have keep₃ (reg : Reg) (a : reg ≠ .x6) :
      (([.ADD .x6 .x25 .x27] : List Instr).foldl execInstrBr s₂).getReg reg = s₂.getReg reg := by
    simp [execInstrBr, get_reg_set_reg, Ne.symm a]
  generalize h₃ : ([.ADD .x6 .x25 .x27] : List Instr).foldl execInstrBr s₂ = s₃ at run₃ pc₃ mem₃ x6₃ keep₃
  -- store
  obtain ⟨run₄, pc₄, view₄, keep₄⟩ := wrap_store wrap s₃ .x6 .x5 0 119 c₄ (by rw [pc₃, pc₂, pc_add]; rfl)
    (proofWord + 178*r + d)
    (by rw [x6₃, keep₂ .x25 (by decide), keep₁ .x25 (by decide), keep₂ .x27 (by decide), keep₁ .x27 (by decide),
          at_.x25, counter, show signExtend12 (0 : BitVec 12) = 0#64 by decide, BitVec.add_zero, ← BitVec.ofNat_add]
        apply word_of_bytes; omega)
    (by omega)
  generalize h₄ : execInstrBr s₃ (.SD .x6 .x5 0) = s₄ at run₄ pc₄ view₄ keep₄
  have stored : s₃.getReg .x5 = expandedWord sub input (178*r + d) := by rw [keep₃ .x5 (by decide), loaded]
  -- decrement and branch
  have pure₅ : ([.ADDI .x27 .x27 4088] : List Instr).all wrapPure = true := rfl
  have run₅ := wrap_pure_run wrap _ 120 s₄ c₅ (by rw [pc₄]) pure₅
  have pc₅ := wrap_pure_pc _ s₄ pure₅
  have mem₅ := wrap_pure_mem _ s₄ pure₅
  have x27₅ : (([.ADDI .x27 .x27 4088] : List Instr).foldl execInstrBr s₄).getReg .x27 =
      s₄.getReg .x27 + signExtend12 4088 := by simp [execInstrBr, get_reg_set_reg]
  have keep₅ (reg : Reg) (a : reg ≠ .x27) :
      (([.ADDI .x27 .x27 4088] : List Instr).foldl execInstrBr s₄).getReg reg = s₄.getReg reg := by
    simp [execInstrBr, get_reg_set_reg, Ne.symm a]
  generalize h₅ : ([.ADDI .x27 .x27 4088] : List Instr).foldl execInstrBr s₄ = s₅ at run₅ pc₅ mem₅ x27₅ keep₅
  have count₅ : s₅.getReg .x27 = BitVec.ofNat 64 (8*d) + signExtend12 4088 := by
    rw [x27₅, keep₄, keep₃ .x27 (by decide), keep₂ .x27 (by decide), keep₁ .x27 (by decide), counter]
  have run₆ := wrap_control wrap s₅ (.BGE .x27 .x0 8172) 121 c₆ (by rw [pc₅, pc₄]; rfl) rfl rfl
  have shape : execInstrBr s₅ (.BGE .x27 .x0 8172) =
      s₅.setPC (if ¬ BitVec.slt (s₅.getReg .x27) (s₅.getReg .x0) then s₅.pc + signExtend13 8172 else s₅.pc + 4) := by
    simp only [execInstrBr]; split <;> rfl
  rw [shape] at run₆
  have regs (reg : Reg) (a : reg ≠ .x5) (b : reg ≠ .x6) (c : reg ≠ .x27) :
      (s₅.setPC (if ¬ BitVec.slt (s₅.getReg .x27) (s₅.getReg .x0) then s₅.pc + signExtend13 8172 else s₅.pc + 4)).getReg reg =
        state.getReg reg := by
    rw [set_pc_reg, keep₅ reg c, keep₄, keep₃ reg b, keep₂ reg a, keep₁ reg a]
  have views (w : Nat) (hw : w < 2^61) :
      memoryView (s₅.setPC (if ¬ BitVec.slt (s₅.getReg .x27) (s₅.getReg .x0) then s₅.pc + signExtend13 8172
        else s₅.pc + 4)) w =
        if w = proofWord + 178*r + d then expandedWord sub input (178*r + d) else memoryView state w := by
    rw [view_of_mem (set_pc_mem _ _), view_of_mem mem₅, view₄ w hw, stored, view_of_mem mem₃, view_of_mem mem₂,
      view_of_mem mem₁]
  have keptNe : ∀ reg ∈ keptRegs, reg ≠ .x5 ∧ reg ≠ .x6 ∧ reg ≠ .x27 := by decide
  have constNe : ∀ reg ∈ constRegs, reg ≠ .x5 ∧ reg ≠ .x6 ∧ reg ≠ .x27 := by decide
  refine ⟨_, (run₁.trans (run₂.trans (run₃.trans (run₄.trans (run₅.trans run₆))))).cast rfl
      (by simp [wrapCost, instructionCycles]), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [regs .x24 (by decide) (by decide) (by decide), at_.x24]
  · rw [regs .x25 (by decide) (by decide) (by decide), at_.x25]
  · rw [regs .x26 (by decide) (by decide) (by decide), at_.x26]
  · exact at_.consts.keep (fun reg member => by obtain ⟨a, b, c⟩ := constNe reg member; exact regs reg a b c)
  · exact at_.kept.keep (fun reg member => by obtain ⟨a, b, c⟩ := keptNe reg member; exact regs reg a b c)
  · intro x hx
    rw [views _ (by omega), if_neg (by omega)]
    exact at_.table x hx
  · intro w hw side
    rw [views _ (by omega), if_neg (by omega)]
    exact at_.low w (by omega) side
  · intro w lo hi
    rw [views _ (by omega)]
    by_cases here : w = proofWord + 178*r + d
    · rw [if_pos here, show w - proofWord = 178*r + d by omega]
    · rw [if_neg here]
      exact at_.copied w (by omega) hi
  · intro w lo hi
    rw [views _ (by omega), if_neg (by omega)]
    exact at_.done w lo hi
  · intro w hw lo
    rw [views _ (by omega), if_neg (by omega)]
    exact at_.high w hw lo
  · rw [set_pc_pc, count₅, show s₅.getReg .x0 = 0#64 from rfl, pc₅, pc₄]
    by_cases last : d = 0
    · subst last
      rw [if_pos rfl, show BitVec.ofNat 64 (8*0) + signExtend12 4088 = BitVec.ofNat 64 (2^64-8) by decide,
        copy_offset_done]
      decide
    · have notOne : ¬ (d + 1 = 1) := by omega
      rw [neg_imm (8*d) 8 4088 (by omega) (by omega) (by decide), show 8*d - 8 = 8*(d-1) by omega,
        copy_offset_small _ (by omega), if_neg notOne]
      decide
  · intro notLast
    rw [set_pc_reg, count₅, neg_imm (8*d) 8 4088 (by omega) (by omega) (by decide)]
    congr 1
    omega


theorem copy_loop {sub : Submission} (wrap : WrapImage (sub.image .check))
    (input : CheckInput) (r : Nat) (present : r < input.positions.card) :
    ∀ j ≤ 114, ∀ state : MachineState, state.pc = BitVec.ofNat 64 (4096+4*(460+116)) →
      state.getReg .x27 = BitVec.ofNat 64 904 → Copying sub input r 114 state →
      ∃ next : MachineState, Hop (sub.image .check) state next (6*j) (6*j) ∧ Copying sub input r (114-j) next ∧
        next.pc = BitVec.ofNat 64 (4096+4*(460+(if j = 114 then 122 else 116))) ∧
        (j < 114 → next.getReg .x27 = BitVec.ofNat 64 (8*(113-j))) := by
  intro j
  induction j with
  | zero => intro _ state pc counter at_; exact ⟨state, Hop.zero _ _, at_, by simpa using pc, fun _ => counter⟩
  | succ j ih =>
    intro le state pc counter at_
    obtain ⟨mid, run, atMid, pcMid, countMid⟩ := ih (by omega) state pc counter at_
    obtain ⟨next, run₂, atNext, pcNext, countNext⟩ := copy_step wrap input r (114-j) present (by omega) (by omega)
      mid (by rw [pcMid, if_neg (by omega)]) (by rw [countMid (by omega)]; congr 1; omega) atMid
    refine ⟨next, (run.trans run₂).cast (by ring) (by ring), by simpa [show 114 - j - 1 = 114 - (j+1) by omega] using atNext,
      ?_, ?_⟩
    · rw [pcNext]
      by_cases last : j + 1 = 114
      · rw [if_pos (by omega), if_pos last]
      · rw [if_neg (by omega), if_neg last]
    · intro notLast
      rw [countNext (by omega)]
      congr 1
      omega

theorem head_code : wrapCode[122]? = some (.LD .x5 .x26 0) ∧ WrapAt 123 [.DIVU .x6 .x5 .x8] := by
  decide +kernel

/-- The record's index and its level-7 quotient. -/
theorem record_head {sub : Submission} (lay : WrapLayout sub) (wrap : WrapImage (sub.image .check))
    (input : CheckInput) (r : Nat) (present : r < input.positions.card)
    (state : MachineState) (pc : state.pc = BitVec.ofNat 64 (4096+4*(460+122)))
    (at_ : Copying sub input r 0 state) :
    ∃ next : MachineState, Hop (sub.image .check) state next 2 5 ∧ Filling sub input r 0 next ∧
      next.pc = BitVec.ofNat 64 (4096+4*(460+124)) := by
  have card : input.positions.card ≤ 16777216 := by
    have : input.positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
    exact this
  obtain ⟨c₁, c₂⟩ := head_code
  have pw : proofWord = 1350566924 := rfl
  have tw : TBW = 33554432 := rfl
  have room : MEMORY_BYTES = 68719476736 := rfl
  obtain ⟨run₁, pc₁, mem₁, x5₁, keep₁⟩ := wrap_load wrap state .x5 .x26 0 122 c₁ pc (8*(796918788 + r))
    (by rw [at_.x26, show signExtend12 (0 : BitVec 12) = 0#64 by decide, BitVec.add_zero]; congr 1; omega)
    (by omega) (by omega)
  generalize h₁ : execInstrBr state (.LD .x5 .x26 0) = s₁ at run₁ pc₁ mem₁ x5₁ keep₁
  have index : s₁.getReg .x5 = BitVec.ofNat 64 (sortedIndex input.positions r) := by
    rw [x5₁, if_neg (by decide)]
    have e : state.getMem (BitVec.ofNat 64 (8*(796918788 + r))) = memoryView state (796918788 + r) := rfl
    rw [e, at_.low _ (by omega) (by right; omega), index_word lay input r present]
  have pure₂ : ([.DIVU .x6 .x5 .x8] : List Instr).all wrapPure = true := rfl
  have run₂ := wrap_pure_run wrap _ 123 s₁ c₂ (by rw [pc₁]) pure₂
  have pc₂ := wrap_pure_pc _ s₁ pure₂
  have mem₂ := wrap_pure_mem _ s₁ pure₂
  have x6₂ : (([.DIVU .x6 .x5 .x8] : List Instr).foldl execInstrBr s₁).getReg .x6 =
      rv64_divu (s₁.getReg .x5) (s₁.getReg .x8) := by simp [execInstrBr, get_reg_set_reg]
  have keep₂ (reg : Reg) (a : reg ≠ .x6) :
      (([.DIVU .x6 .x5 .x8] : List Instr).foldl execInstrBr s₁).getReg reg = s₁.getReg reg := by
    simp [execInstrBr, get_reg_set_reg, Ne.symm a]
  generalize h₂ : ([.DIVU .x6 .x5 .x8] : List Instr).foldl execInstrBr s₁ = s₂ at run₂ pc₂ mem₂ x6₂ keep₂
  have regs (reg : Reg) (a : reg ≠ .x5) (b : reg ≠ .x6) : s₂.getReg reg = state.getReg reg := by
    rw [keep₂ reg b, keep₁ reg a]
  have keptNe : ∀ reg ∈ keptRegs, reg ≠ .x5 ∧ reg ≠ .x6 := by decide
  have constNe : ∀ reg ∈ constRegs, reg ≠ .x5 ∧ reg ≠ .x6 := by decide
  have small := sorted_index_small input.positions r
  refine ⟨s₂, (run₁.trans run₂).cast rfl (by simp [wrapCost, instructionCycles]),
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [regs .x24 (by decide) (by decide), at_.x24]
  · rw [regs .x25 (by decide) (by decide), at_.x25]
  · rw [regs .x26 (by decide) (by decide), at_.x26]
  · rw [x6₂, index, keep₁ .x8 (by decide), at_.consts.q7, divu_value _ _ (by decide) (by omega) (by decide),
      cap_quot_zero]
  · exact at_.consts.keep (fun reg member => by obtain ⟨a, b⟩ := constNe reg member; exact regs reg a b)
  · exact at_.kept.keep (fun reg member => by obtain ⟨a, b⟩ := keptNe reg member; exact regs reg a b)
  · intro x hx; rw [view_of_mem mem₂, view_of_mem mem₁]; exact at_.table x hx
  · intro w hw side; rw [view_of_mem mem₂, view_of_mem mem₁]; exact at_.low w (by omega) side
  · intro w lo hi; rw [view_of_mem mem₂, view_of_mem mem₁]; exact at_.copied w (by omega) (by omega)
  · intro w lo hi; rw [view_of_mem mem₂, view_of_mem mem₁]; exact at_.done w lo hi
  · intro w hw lo; rw [view_of_mem mem₂, view_of_mem mem₁]; exact at_.high w hw lo
  · rw [pc₂, pc₁, pc_add]
    rfl

theorem record_fills {sub : Submission} (wrap : WrapImage (sub.image .check)) (input : CheckInput)
    (r : Nat) (present : r < input.positions.card) :
    ∀ lvl ≤ 4, ∀ state : MachineState, state.pc = BitVec.ofNat 64 (4096+4*(460+124)) →
      Filling sub input r 0 state →
      ∃ next : MachineState, Hop (sub.image .check) state next (40*lvl) (49*lvl) ∧ Filling sub input r lvl next ∧
        next.pc = BitVec.ofNat 64 (4096+4*(460+(124+40*lvl))) := by
  intro lvl
  induction lvl with
  | zero => intro _ state pc at_; exact ⟨state, Hop.zero _ _, at_, by simpa using pc⟩
  | succ lvl ih =>
    intro le state pc at_
    obtain ⟨mid, run, atMid, pcMid⟩ := ih (by omega) state pc at_
    obtain ⟨next, run₂, atNext, pcNext⟩ := level_fill wrap input r lvl present (by omega) mid pcMid atMid
    exact ⟨next, (run.trans run₂).cast (by ring) (by ring), atNext, pcNext⟩

theorem ult_small (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) :
    BitVec.ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a < b) := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem latch_code : WrapAt 284 [.ADDI .x24 .x24 3184, .ADDI .x25 .x25 2672, .ADDI .x26 .x26 4088] ∧
    wrapCode[287]? = some (.BGEU .x26 .x13 7504) := by
  decide +kernel

/-- Pointers to the previous record, and the loop test. -/
theorem record_latch {sub : Submission} (lay : WrapLayout sub) (wrap : WrapImage (sub.image .check)) (input : CheckInput)
    (r : Nat) (present : r < input.positions.card)
    (state : MachineState) (pc : state.pc = BitVec.ofNat 64 (4096+4*(460+(124+40*4))))
    (at_ : Filling sub input r 4 state) :
    ∃ next : MachineState, Hop (sub.image .check) state next 4 4 ∧ Expanding sub input r next ∧
      next.pc = BitVec.ofNat 64 (4096+4*(460+(if r = 0 then 288 else 115))) := by
  have card : input.positions.card ≤ 16777216 := by
    have : input.positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
    exact this
  have pb : PENTA_PROOF_BASE = 10804535392 := rfl
  obtain ⟨c₁, c₂⟩ := latch_code
  have pure₁ : ([.ADDI .x24 .x24 3184, .ADDI .x25 .x25 2672, .ADDI .x26 .x26 4088] : List Instr).all wrapPure = true := rfl
  have run₁ := wrap_pure_run wrap _ 284 state c₁ pc pure₁
  have pc₁ := wrap_pure_pc _ state pure₁
  have mem₁ := wrap_pure_mem _ state pure₁
  have x24₁ : (([.ADDI .x24 .x24 3184, .ADDI .x25 .x25 2672, .ADDI .x26 .x26 4088] : List Instr).foldl execInstrBr state).getReg .x24 =
      state.getReg .x24 + signExtend12 3184 := by simp [execInstrBr, get_reg_set_reg]
  have x25₁ : (([.ADDI .x24 .x24 3184, .ADDI .x25 .x25 2672, .ADDI .x26 .x26 4088] : List Instr).foldl execInstrBr state).getReg .x25 =
      state.getReg .x25 + signExtend12 2672 := by simp [execInstrBr, get_reg_set_reg]
  have x26₁ : (([.ADDI .x24 .x24 3184, .ADDI .x25 .x25 2672, .ADDI .x26 .x26 4088] : List Instr).foldl execInstrBr state).getReg .x26 =
      state.getReg .x26 + signExtend12 4088 := by simp [execInstrBr, get_reg_set_reg]
  have keep₁ (reg : Reg) (a : reg ≠ .x24) (b : reg ≠ .x25) (c : reg ≠ .x26) :
      (([.ADDI .x24 .x24 3184, .ADDI .x25 .x25 2672, .ADDI .x26 .x26 4088] : List Instr).foldl execInstrBr state).getReg reg =
        state.getReg reg := by
    simp [execInstrBr, get_reg_set_reg, Ne.symm a, Ne.symm b, Ne.symm c]
  generalize h₁ : ([.ADDI .x24 .x24 3184, .ADDI .x25 .x25 2672, .ADDI .x26 .x26 4088] : List Instr).foldl execInstrBr state = s₁
    at run₁ pc₁ mem₁ x24₁ x25₁ x26₁ keep₁
  have p24 : s₁.getReg .x24 = BitVec.ofNat 64 (PENTA_PROOF_BASE + 912*r - 912) := by
    rw [x24₁, at_.x24, neg_imm _ 912 3184 (by omega) (by omega) (by decide)]
  have p25 : s₁.getReg .x25 = BitVec.ofNat 64 (PENTA_PROOF_BASE + 1424*r - 1424) := by
    rw [x25₁, at_.x25, neg_imm _ 1424 2672 (by omega) (by omega) (by decide)]
  have p26 : s₁.getReg .x26 = BitVec.ofNat 64 (6375350304 + 8*r - 8) := by
    rw [x26₁, at_.x26, neg_imm _ 8 4088 (by omega) (by omega) (by decide)]
  have x13 : s₁.getReg .x13 = BitVec.ofNat 64 6375350304 := by
    rw [keep₁ .x13 (by decide) (by decide) (by decide), at_.kept .x13 (by decide), loader_reg lay input .x13]
    rfl
  have run₂ := wrap_control wrap s₁ (.BGEU .x26 .x13 7504) 287 c₂ (by rw [pc₁, pc, pc_add]; rfl) rfl rfl
  have shape : execInstrBr s₁ (.BGEU .x26 .x13 7504) =
      s₁.setPC (if ¬ BitVec.ult (s₁.getReg .x26) (s₁.getReg .x13) then s₁.pc + signExtend13 7504 else s₁.pc + 4) := by
    simp only [execInstrBr]; split <;> rfl
  rw [shape] at run₂
  have keptNe : ∀ reg ∈ keptRegs, reg ≠ .x24 ∧ reg ≠ .x25 ∧ reg ≠ .x26 := by decide
  have constNe : ∀ reg ∈ constRegs, reg ≠ .x24 ∧ reg ≠ .x25 ∧ reg ≠ .x26 := by decide
  refine ⟨_, (run₁.trans run₂).cast rfl (by simp [wrapCost, instructionCycles]), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [set_pc_reg, p24]
  · rw [set_pc_reg, p25]
  · rw [set_pc_reg, p26]
  · exact at_.consts.keep (fun reg member => by
      obtain ⟨a, b, c⟩ := constNe reg member; rw [set_pc_reg, keep₁ reg a b c])
  · exact at_.kept.keep (fun reg member => by
      obtain ⟨a, b, c⟩ := keptNe reg member; rw [set_pc_reg, keep₁ reg a b c])
  · intro x hx; rw [view_of_mem (set_pc_mem _ _), view_of_mem mem₁]; exact at_.table x hx
  · intro w hw side; rw [view_of_mem (set_pc_mem _ _), view_of_mem mem₁]; exact at_.low w hw side
  · intro w lo hi
    rw [view_of_mem (set_pc_mem _ _), view_of_mem mem₁]
    by_cases mine : w < proofWord + 178*r + 178
    · exact at_.filled w lo (by omega)
    · exact at_.done w (by omega) hi
  · intro w hw lo; rw [view_of_mem (set_pc_mem _ _), view_of_mem mem₁]; exact at_.high w hw lo
  · rw [set_pc_pc, p26, x13, pc₁, pc, pc_add]
    have small : 6375350304 + 8*r - 8 < 2^64 := by omega
    rw [ult_small _ _ small (by decide)]
    by_cases zero : r = 0
    · subst zero
      rw [if_pos rfl]
      decide
    · rw [if_neg zero, show decide (6375350304 + 8*r - 8 < 6375350304) = false by simp; omega]
      decide


theorem record_start_code : WrapAt 115 [.ADDI .x27 .x0 904] := by decide +kernel

/-- One whole record. -/
theorem record_step {sub : Submission} (lay : WrapLayout sub) (wrap : WrapImage (sub.image .check))
    (input : CheckInput) (r : Nat) (present : r < input.positions.card)
    (state : MachineState) (pc : state.pc = BitVec.ofNat 64 (4096+4*(460+115)))
    (at_ : Expanding sub input (r+1) state) :
    ∃ next : MachineState, Hop (sub.image .check) state next 851 890 ∧ Expanding sub input r next ∧
      next.pc = BitVec.ofNat 64 (4096+4*(460+(if r = 0 then 288 else 115))) := by
  have pure₁ : ([.ADDI .x27 .x0 904] : List Instr).all wrapPure = true := rfl
  have run₁ := wrap_pure_run wrap _ 115 state record_start_code pc pure₁
  have pc₁ := wrap_pure_pc _ state pure₁
  have mem₁ := wrap_pure_mem _ state pure₁
  have x27₁ : (([.ADDI .x27 .x0 904] : List Instr).foldl execInstrBr state).getReg .x27 = BitVec.ofNat 64 904 := by
    have z : state.getReg .x0 = 0#64 := rfl
    simp [execInstrBr, get_reg_set_reg, z]
    decide
  have keep₁ (reg : Reg) (a : reg ≠ .x27) :
      (([.ADDI .x27 .x0 904] : List Instr).foldl execInstrBr state).getReg reg = state.getReg reg := by
    simp [execInstrBr, get_reg_set_reg, Ne.symm a]
  generalize h₁ : ([.ADDI .x27 .x0 904] : List Instr).foldl execInstrBr state = s₁ at run₁ pc₁ mem₁ x27₁ keep₁
  have keptNe : ∀ reg ∈ keptRegs, reg ≠ .x27 := by decide
  have constNe : ∀ reg ∈ constRegs, reg ≠ .x27 := by decide
  have copying : Copying sub input r 114 s₁ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [keep₁ .x24 (by decide), at_.x24]; congr 1 <;> omega
    · rw [keep₁ .x25 (by decide), at_.x25]; congr 1 <;> omega
    · rw [keep₁ .x26 (by decide), at_.x26]; congr 1 <;> omega
    · exact at_.consts.keep (fun reg member => keep₁ reg (constNe reg member))
    · exact at_.kept.keep (fun reg member => keep₁ reg (keptNe reg member))
    · intro x hx; rw [view_of_mem mem₁]; exact at_.table x hx
    · intro w hw side; rw [view_of_mem mem₁]; exact at_.low w (by omega) side
    · intro w lo hi; omega
    · intro w lo hi; rw [view_of_mem mem₁]; exact at_.done w (by omega) hi
    · intro w hw lo; rw [view_of_mem mem₁]; exact at_.high w hw lo
  obtain ⟨s₂, run₂, at₂, pc₂, _⟩ := copy_loop wrap input r present 114 le_rfl s₁
    (by rw [pc₁, pc, pc_add]; rfl) x27₁ copying
  obtain ⟨s₃, run₃, at₃, pc₃⟩ := record_head lay wrap input r present s₂ (by rw [pc₂]; rfl) at₂
  obtain ⟨s₄, run₄, at₄, pc₄⟩ := record_fills wrap input r present 4 le_rfl s₃ pc₃ at₃
  obtain ⟨s₅, run₅, at₅, pc₅⟩ := record_latch lay wrap input r present s₄ pc₄ at₄
  exact ⟨s₅, (run₁.trans (run₂.trans (run₃.trans (run₄.trans run₅)))).cast (by simp) (by simp [wrapCost,
    instructionCycles]), at₅, pc₅⟩

/-- All records, from the last one down. -/
theorem records_loop {sub : Submission} (lay : WrapLayout sub) (wrap : WrapImage (sub.image .check))
    (input : CheckInput) :
    ∀ j ≤ input.positions.card, ∀ state : MachineState, input.positions.card ≠ 0 →
      state.pc = BitVec.ofNat 64 (4096+4*(460+115)) → Expanding sub input input.positions.card state →
      ∃ next : MachineState, Hop (sub.image .check) state next (851*j) (890*j) ∧
        Expanding sub input (input.positions.card - j) next ∧
        next.pc = BitVec.ofNat 64 (4096+4*(460+(if j = input.positions.card then 288 else 115))) := by
  intro j
  induction j with
  | zero =>
    intro _ state nonempty pc at_
    exact ⟨state, Hop.zero _ _, by simpa using at_, by rw [if_neg (by omega)]; exact pc⟩
  | succ j ih =>
    intro le state nonempty pc at_
    obtain ⟨mid, run, atMid, pcMid⟩ := ih (by omega) state nonempty pc at_
    have pcLoop : mid.pc = BitVec.ofNat 64 (4096+4*(460+115)) := by rw [pcMid, if_neg (by omega)]
    obtain ⟨next, run₂, atNext, pcNext⟩ := record_step lay wrap input (input.positions.card - (j+1)) (by omega) mid
      pcLoop (by rw [show input.positions.card - (j+1) + 1 = input.positions.card - j by omega]; exact atMid)
    refine ⟨next, (run.trans run₂).cast (by ring) (by ring), atNext, ?_⟩
    rw [pcNext]
    by_cases last : j + 1 = input.positions.card
    · rw [if_pos (by omega), if_pos last]
    · rw [if_neg (by omega), if_neg last]

end TwoPermutationPrototype.PentaWrap
