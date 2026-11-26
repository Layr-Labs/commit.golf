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
  x24 : state.getReg .x24 = BitVec.ofNat 64 (PENTA_PROOF_BASE + 1136*r)
  x25 : state.getReg .x25 = BitVec.ofNat 64 (PENTA_PROOF_BASE + 1424*r)
  x26 : state.getReg .x26 = BitVec.ofNat 64 (6375350304 + 8*r)
  x6 : state.getReg .x6 = BitVec.ofNat 64 (capQuot (sortedIndex input.positions r) lvl)
  consts : Consts state
  kept : Kept (sub.initialState .check input) state
  table : ∀ x < 2200, memoryView state (TBW + x) = tableWord sub input x
  low : ∀ w < proofWord + 142*r, (w < TBW ∨ TBW + 2200 ≤ w) →
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
  x24 : state.getReg .x24 = BitVec.ofNat 64 (PENTA_PROOF_BASE + 1136*r)
  x25 : state.getReg .x25 = BitVec.ofNat 64 (PENTA_PROOF_BASE + 1424*r)
  x26 : state.getReg .x26 = BitVec.ofNat 64 (6375350304 + 8*r)
  x7 : state.getReg .x7 = BitVec.ofNat 64 (capQuot (sortedIndex input.positions r) lvl / 5)
  x29 : state.getReg .x29 = wordAddress (TBW + 40*(capFirst lvl + capQuot (sortedIndex input.positions r) lvl / 5) +
    4*(capQuot (sortedIndex input.positions r) lvl % 5 + 1))
  consts : Consts state
  kept : Kept (sub.initialState .check input) state
  table : ∀ x < 2200, memoryView state (TBW + x) = tableWord sub input x
  low : ∀ w < proofWord + 142*r, (w < TBW ∨ TBW + 2200 ≤ w) →
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
    rw [v₁, v₂, if_neg (by omega), if_neg (by omega)]
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
  x24 : state.getReg .x24 = BitVec.ofNat 64 (PENTA_PROOF_BASE + 1136*r - 1136)
  x25 : state.getReg .x25 = BitVec.ofNat 64 (PENTA_PROOF_BASE + 1424*r - 1424)
  x26 : state.getReg .x26 = BitVec.ofNat 64 (6375350304 + 8*r - 8)
  consts : Consts state
  kept : Kept (sub.initialState .check input) state
  table : ∀ x < 2200, memoryView state (TBW + x) = tableWord sub input x
  low : ∀ w < proofWord + 142*r, (w < TBW ∨ TBW + 2200 ≤ w) →
    memoryView state w = memoryView (sub.initialState .check input) w
  done : ∀ w, proofWord + 178*r ≤ w → w < proofWord + 178*input.positions.card →
    memoryView state w = expandedWord sub input (w - proofWord)
  high : ∀ w < 2^33, proofWord + 178*input.positions.card ≤ w → memoryView state w = 0

/-- Copying record `r`: `n` prefix doublewords are still to be copied. -/
structure Copying (sub : Submission) (input : CheckInput) (r n : Nat) (state : MachineState) : Prop where
  x24 : state.getReg .x24 = BitVec.ofNat 64 (PENTA_PROOF_BASE + 1136*r)
  x25 : state.getReg .x25 = BitVec.ofNat 64 (PENTA_PROOF_BASE + 1424*r)
  x26 : state.getReg .x26 = BitVec.ofNat 64 (6375350304 + 8*r)
  consts : Consts state
  kept : Kept (sub.initialState .check input) state
  table : ∀ x < 2200, memoryView state (TBW + x) = tableWord sub input x
  low : ∀ w < proofWord + 142*r + n, (w < TBW ∨ TBW + 2200 ≤ w) →
    memoryView state w = memoryView (sub.initialState .check input) w
  copied : ∀ w, proofWord + 178*r + n ≤ w → w < proofWord + 178*r + 114 →
    memoryView state w = expandedWord sub input (w - proofWord)
  done : ∀ w, proofWord + 178*(r+1) ≤ w → w < proofWord + 178*input.positions.card →
    memoryView state w = expandedWord sub input (w - proofWord)
  high : ∀ w < 2^33, proofWord + 178*input.positions.card ≤ w → memoryView state w = 0

/-! ### The record body (wrapper offsets 3470-4465)

Offset 115 jumps to the body. The body doubles the seven level groups of compressed record `r`
(`142 r + 2 + 20 k + m`) into the scratch buffer at word `RSW + 40 k + m` and `+20`, copies the
salt, writes the four other slots of each level in rotation order from the doubled groups, clears
the scratch buffer and jumps back to offset 122. -/

def RSW : Nat := 33562624

theorem rs_word : RS = 8*RSW := rfl

private theorem rs_byte {sub : Submission} (lay : WrapLayout sub) (input : CheckInput) (address : Nat)
    (low : address < 4294971392) : inputByte sub .check input address = 0 := by
  have base := data_base_value lay
  have hc : sub.layout.commitment = 4294971392 := by rw [lay.layout]
  have hi : sub.layout.indices = 6375350304 := by rw [lay.layout]
  have hv : sub.layout.values = 6509568096 := by rw [lay.layout]
  have hp : sub.layout.proof = 10804535392 := by rw [lay.layout]
  have e₁ : (DIGEST_BITS + 7) / 8 = 32 := rfl
  have e₂ : LEAF_SIZE / 8 = 256 := rfl
  have no₁ : ¬ (4294971392 ≤ address ∧ address < 4294971392 + 32) := by omega
  have no₂ : ¬ (6375350304 ≤ address ∧ address < 6375350304 + 8 * input.positions.card) := by omega
  have no₃ : ¬ (6509568096 ≤ address ∧ address < 6509568096 + 256 * input.positions.card) := by omega
  have no₄ : ¬ (10804535392 ≤ address ∧ address < 10804535392 + input.proof.length) := by omega
  unfold inputByte
  simp only [Submission.inputBuffers, hc, hi, hv, hp, fixedBuffer, positionsBuffer, valuesBuffer,
    Finset.length_sort, Finset.card_attach, e₁, e₂,
    List.find?_cons, List.find?_nil, no₁, no₂, no₃, no₄, decide_false, base, lay.data]
  split <;> simp

theorem rs_loader_zero {sub : Submission} (lay : WrapLayout sub) (input : CheckInput) (w : Nat)
    (low : 8*w + 8 ≤ 4294971392) : memoryView (sub.initialState .check input) w = 0 := by
  rw [loader_word _ w (by omega)]
  have h (j : Nat) (hj : j ∈ Finset.range 8) :
      (inputByte sub .check input (8*w+j)).toNat * 2^(8*j) = 0 := by
    rw [rs_byte lay input _ (by have := Finset.mem_range.mp hj; omega)]; simp
  rw [Finset.sum_eq_zero h]; rfl

/-- Scratch word `x < 280` once the first `n` group doublewords of record `r` are doubled. -/
def rsWord (sub : Submission) (input : CheckInput) (r n x : Nat) : Word :=
  if 20*(x/40) + x%40%20 < n then sourceWord sub input (142*r + 2 + 20*(x/40) + x%40%20) else 0

/-- Record `r` in the body: `n` doublewords doubled, `f` expanded words written, `c` scratch words
cleared. -/
structure Body (sub : Submission) (input : CheckInput) (r n f c : Nat) (state : MachineState) : Prop where
  x24 : state.getReg .x24 = BitVec.ofNat 64 (PENTA_PROOF_BASE + 1136*r)
  x25 : state.getReg .x25 = BitVec.ofNat 64 (PENTA_PROOF_BASE + 1424*r)
  x26 : state.getReg .x26 = BitVec.ofNat 64 (6375350304 + 8*r)
  consts : Consts state
  kept : Kept (sub.initialState .check input) state
  table : ∀ x < 2200, memoryView state (TBW + x) = tableWord sub input x
  rs : ∀ x < 280, memoryView state (RSW + x) = if x < c then 0 else rsWord sub input r n x
  low : ∀ w < proofWord + 142*r + (if f = 0 then 142 else 0), (w < TBW ∨ TBW + 2200 ≤ w) →
    (w < RSW ∨ RSW + 280 ≤ w) → memoryView state w = memoryView (sub.initialState .check input) w
  filled : ∀ w, proofWord + 178*r ≤ w → w < proofWord + 178*r + f →
    memoryView state w = expandedWord sub input (w - proofWord)
  done : ∀ w, proofWord + 178*(r+1) ≤ w → w < proofWord + 178*input.positions.card →
    memoryView state w = expandedWord sub input (w - proofWord)
  high : ∀ w < 2^33, proofWord + 178*input.positions.card ≤ w → memoryView state w = 0

def bodyScratch : List Reg := [.x5, .x6, .x7, .x27, .x28, .x29, .x30, .x31]

theorem Body.keep {sub : Submission} {input : CheckInput} {r n f c : Nat} {a b : MachineState}
    (h : Body sub input r n f c a) (mem : b.mem = a.mem)
    (regs : ∀ reg, reg ∉ bodyScratch → b.getReg reg = a.getReg reg) : Body sub input r n f c b := by
  have keptNe : ∀ reg ∈ keptRegs, reg ∉ bodyScratch := by decide
  have constNe : ∀ reg ∈ constRegs, reg ∉ bodyScratch := by decide
  refine ⟨?_, ?_, ?_, h.consts.keep (fun reg m => regs reg (constNe reg m)),
    h.kept.keep (fun reg m => regs reg (keptNe reg m)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [regs .x24 (by decide), h.x24]
  · rw [regs .x25 (by decide), h.x25]
  · rw [regs .x26 (by decide), h.x26]
  · intro x hx; rw [view_of_mem mem]; exact h.table x hx
  · intro x hx; rw [view_of_mem mem]; exact h.rs x hx
  · intro w hw s₁ s₂; rw [view_of_mem mem]; exact h.low w hw s₁ s₂
  · intro w lo hi; rw [view_of_mem mem]; exact h.filled w lo hi
  · intro w lo hi; rw [view_of_mem mem]; exact h.done w lo hi
  · intro w hw lo; rw [view_of_mem mem]; exact h.high w hw lo

theorem wrap_code_body : ∃ head : List Instr, head.length = 3470 ∧ wrapCode = head ++ bodyCode :=
  ⟨guardCode ++ tableGroupCode ++ tableLatchCode ++ (.JAL .x0 884 :: constantCode.tail) ++ pointerCode ++
    copyCode ++ (List.range 4).flatMap levelFill ++ latchCode ++ restoreCode ++ emptyCode ++ rejectCode ++ hashCode,
    by decide, by simp only [wrapCode, List.append_assoc]⟩

theorem wrap_body (i : Nat) : wrapCode[3470+i]? = bodyCode[i]? := by
  obtain ⟨head, len, split⟩ := wrap_code_body
  rw [split, List.getElem?_append_right (by omega), len, Nat.add_sub_cancel_left]

set_option maxRecDepth 200000 in
theorem body_codes_a :
    bodyCode[0]? = some (.LUI .x27 65552) ∧
    (∀ k < 7, ∀ m < 20, bodyCode[1+61*k+3*m]? = some (.LD .x5 .x24 (BitVec.ofNat 12 (16+160*k+8*m))) ∧
      bodyCode[1+61*k+3*m+1]? = some (.SD .x27 .x5 (BitVec.ofNat 12 (8*m))) ∧
      bodyCode[1+61*k+3*m+2]? = some (.SD .x27 .x5 (BitVec.ofNat 12 (160+8*m)))) ∧
    (∀ k < 7, bodyCode[1+61*k+60]? = some (.ADDI .x27 .x27 320)) := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem body_codes_b :
    bodyCode[428]? = some (.LD .x5 .x24 0) ∧ bodyCode[429]? = some (.SD .x25 .x5 0) ∧
    bodyCode[430]? = some (.LD .x5 .x24 8) ∧ bodyCode[431]? = some (.SD .x25 .x5 8) ∧
    bodyCode[432]? = some (.LD .x6 .x26 0) ∧ bodyCode[433]? = some (.LUI .x30 65552) := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem body_codes_c : ∀ k < 7, bodyCode[434+39*k]? = some (.DIVU .x7 .x6 .x9) ∧
      bodyCode[434+39*k+1]? = some (.MUL .x28 .x7 .x9) ∧
      bodyCode[434+39*k+2]? = some (.SUB .x28 .x6 .x28) ∧ bodyCode[434+39*k+3]? = some (.SLLI .x28 .x28 5) ∧
      bodyCode[434+39*k+4]? = some (.ADD .x29 .x28 .x30) ∧
      bodyCode[434+39*k+37]? = some (.ADDI .x6 .x7 0) ∧ bodyCode[434+39*k+38]? = some (.ADDI .x30 .x30 320) := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem body_codes_d : ∀ k < 7, ∀ m < 16, bodyCode[434+39*k+5+2*m]? = some (.LD .x31 .x29 (BitVec.ofNat 12 (32+8*m))) ∧
        bodyCode[434+39*k+5+2*m+1]? = some (.SD .x25 .x31 (BitVec.ofNat 12 (16+128*k+8*m))) := by
  decide +kernel

set_option maxRecDepth 200000 in
theorem body_codes_e :
    bodyCode[707]? = some (.LUI .x27 65552) ∧
    (∀ k < 7, (∀ m < 40, bodyCode[708+41*k+m]? = some (.SD .x27 .x0 (BitVec.ofNat 12 (8*m)))) ∧
      bodyCode[708+41*k+40]? = some (.ADDI .x27 .x27 320)) ∧
    bodyCode[995]? = some (.JAL .x0 2079780) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem copy_jump : wrapCode[115]? = some (.JAL .x0 13420) := by decide +kernel

theorem body_codes :
    wrapCode[115]? = some (.JAL .x0 13420) ∧ WrapAt 3470 [.LUI .x27 65552] ∧
    (∀ k < 7, ∀ m < 20, wrapCode[3471+61*k+3*m]? = some (.LD .x5 .x24 (BitVec.ofNat 12 (16+160*k+8*m))) ∧
      wrapCode[3471+61*k+3*m+1]? = some (.SD .x27 .x5 (BitVec.ofNat 12 (8*m))) ∧
      wrapCode[3471+61*k+3*m+2]? = some (.SD .x27 .x5 (BitVec.ofNat 12 (160+8*m)))) ∧
    (∀ k < 7, WrapAt (3471+61*k+60) [.ADDI .x27 .x27 320]) ∧
    wrapCode[3898]? = some (.LD .x5 .x24 0) ∧ wrapCode[3899]? = some (.SD .x25 .x5 0) ∧
    wrapCode[3900]? = some (.LD .x5 .x24 8) ∧ wrapCode[3901]? = some (.SD .x25 .x5 8) ∧
    wrapCode[3902]? = some (.LD .x6 .x26 0) ∧ WrapAt 3903 [.LUI .x30 65552] ∧
    (∀ k < 7, WrapAt (3904+39*k)
        [.DIVU .x7 .x6 .x9, .MUL .x28 .x7 .x9, .SUB .x28 .x6 .x28, .SLLI .x28 .x28 5, .ADD .x29 .x28 .x30] ∧
      (∀ m < 16, wrapCode[3904+39*k+5+2*m]? = some (.LD .x31 .x29 (BitVec.ofNat 12 (32+8*m))) ∧
        wrapCode[3904+39*k+5+2*m+1]? = some (.SD .x25 .x31 (BitVec.ofNat 12 (16+128*k+8*m)))) ∧
      WrapAt (3904+39*k+37) [.ADDI .x6 .x7 0, .ADDI .x30 .x30 320]) ∧
    WrapAt 4177 [.LUI .x27 65552] ∧
    (∀ k < 7, (∀ m < 40, wrapCode[4178+41*k+m]? = some (.SD .x27 .x0 (BitVec.ofNat 12 (8*m)))) ∧
      WrapAt (4178+41*k+40) [.ADDI .x27 .x27 320]) ∧
    wrapCode[4465]? = some (.JAL .x0 2079780) := by
  obtain ⟨b0, bd, ba⟩ := body_codes_a
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := body_codes_b
  obtain ⟨c0, clr, j⟩ := body_codes_e
  have rot := fun k (hk : k < 7) => And.intro (body_codes_c k hk) (body_codes_d k hk)
  have at_ (n : Nat) : wrapCode[3470+n]? = bodyCode[n]? := wrap_body n
  refine ⟨copy_jump, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi; have : i = 0 := by simpa using hi
    subst this; simpa using (at_ 0).trans b0
  · intro k hk m hm
    obtain ⟨x, y, z⟩ := bd k hk m hm
    refine ⟨?_, ?_, ?_⟩
    · rw [show 3471+61*k+3*m = 3470+(1+61*k+3*m) by omega, at_]; exact x
    · rw [show 3471+61*k+3*m+1 = 3470+(1+61*k+3*m+1) by omega, at_]; exact y
    · rw [show 3471+61*k+3*m+2 = 3470+(1+61*k+3*m+2) by omega, at_]; exact z
  · intro k hk i hi
    have : i = 0 := by simpa using hi
    subst this
    rw [show 3471+61*k+60+0 = 3470+(1+61*k+60) by omega, at_]; simpa using ba k hk
  · rw [show 3898 = 3470+428 by rfl, at_]; exact s0
  · rw [show 3899 = 3470+429 by rfl, at_]; exact s1
  · rw [show 3900 = 3470+430 by rfl, at_]; exact s2
  · rw [show 3901 = 3470+431 by rfl, at_]; exact s3
  · rw [show 3902 = 3470+432 by rfl, at_]; exact s4
  · intro i hi; have : i = 0 := by simpa using hi
    subst this; rw [show 3903+0 = 3470+433 by rfl, at_]; simpa using s5
  · intro k hk
    obtain ⟨⟨r0, r1, r2, r3, r4, t0, t1⟩, pairs⟩ := rot k hk
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      have hi' : i < 5 := by simpa using hi
      rw [show 3904+39*k+i = 3470+(434+39*k+i) by omega, at_]
      interval_cases i
      · simpa using r0
      · simpa using r1
      · simpa using r2
      · simpa using r3
      · simpa using r4
    · intro m hm
      obtain ⟨x, y⟩ := pairs m hm
      refine ⟨?_, ?_⟩
      · rw [show 3904+39*k+5+2*m = 3470+(434+39*k+5+2*m) by omega, at_]; exact x
      · rw [show 3904+39*k+5+2*m+1 = 3470+(434+39*k+5+2*m+1) by omega, at_]; exact y
    · intro i hi
      have hi' : i < 2 := by simpa using hi
      rw [show 3904+39*k+37+i = 3470+(434+39*k+37+i) by omega, at_]
      interval_cases i
      · simpa using t0
      · simpa using t1
  · intro i hi; have : i = 0 := by simpa using hi
    subst this; rw [show 4177+0 = 3470+707 by rfl, at_]; simpa using c0
  · intro k hk
    obtain ⟨x, y⟩ := clr k hk
    refine ⟨fun m hm => ?_, ?_⟩
    · rw [show 4178+41*k+m = 3470+(708+41*k+m) by omega, at_]; exact x m hm
    · intro i hi; have : i = 0 := by simpa using hi
      subst this; rw [show 4178+41*k+40+0 = 3470+(708+41*k+40) by omega, at_]; simpa using y
  · rw [show 4465 = 3470+995 by rfl, at_]; exact j

theorem body_offsets :
    (∀ k < 7, ∀ m < 20, signExtend12 (BitVec.ofNat 12 (16+160*k+8*m)) = BitVec.ofNat 64 (16+160*k+8*m) ∧
      signExtend12 (BitVec.ofNat 12 (8*m)) = BitVec.ofNat 64 (8*m) ∧
      signExtend12 (BitVec.ofNat 12 (160+8*m)) = BitVec.ofNat 64 (160+8*m)) ∧
    (∀ k < 7, ∀ m < 16, signExtend12 (BitVec.ofNat 12 (32+8*m)) = BitVec.ofNat 64 (32+8*m) ∧
      signExtend12 (BitVec.ofNat 12 (16+128*k+8*m)) = BitVec.ofNat 64 (16+128*k+8*m)) ∧
    (∀ m < 40, signExtend12 (BitVec.ofNat 12 (8*m)) = BitVec.ofNat 64 (8*m)) ∧
    signExtend12 (320 : BitVec 12) = BitVec.ofNat 64 320 ∧ signExtend12 (8 : BitVec 12) = BitVec.ofNat 64 8 ∧
    signExtend12 (0 : BitVec 12) = 0#64 ∧
    ((BitVec.ofNat 20 65552).zeroExtend 32 <<< 12).signExtend 64 = BitVec.ofNat 64 RS := by
  decide

private theorem card_small (input : CheckInput) : input.positions.card ≤ 16777216 := by
  have : input.positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
  exact this

/-- One doubled doubleword. -/
theorem dbl_step {sub : Submission} (wrap : WrapImage (sub.image .check)) (input : CheckInput)
    (r k m : Nat) (present : r < input.positions.card) (hk : k < 7) (hm : m < 20)
    (state : MachineState) (pc : state.pc = BitVec.ofNat 64 (4096+4*(460+(3471+61*k+3*m))))
    (x27 : state.getReg .x27 = BitVec.ofNat 64 (RS + 320*k))
    (at_ : Body sub input r (20*k+m) 0 0 state) :
    ∃ next : MachineState, Hop (sub.image .check) state next 3 3 ∧ Body sub input r (20*k+m+1) 0 0 next ∧
      next.getReg .x27 = BitVec.ofNat 64 (RS + 320*k) ∧
      next.pc = BitVec.ofNat 64 (4096+4*(460+(3471+61*k+3*(m+1)))) := by
  have card := card_small input
  have pw : proofWord = 1350566924 := rfl
  have pb : PENTA_PROOF_BASE = 10804535392 := rfl
  have tw : TBW = 33554432 := rfl
  have rw' : RSW = 33562624 := rfl
  have rsv : RS = 268500992 := rfl
  have room : MEMORY_BYTES = 68719476736 := rfl
  obtain ⟨_, _, dbl, _⟩ := body_codes
  obtain ⟨c₁, c₂, c₃⟩ := dbl k hk m hm
  obtain ⟨offs, _⟩ := body_offsets
  obtain ⟨o₁, o₂, o₃⟩ := offs k hk m hm
  let src := proofWord + 142*r + 2 + 20*k + m
  obtain ⟨run₁, pc₁, mem₁, x5₁, keep₁⟩ := wrap_load wrap state .x5 .x24 _ _ c₁ pc (8*src)
    (by rw [at_.x24, o₁, ← BitVec.ofNat_add]; apply congrArg (BitVec.ofNat 64); simp only [src]; omega) (by omega) (by simp only [src]; omega)
  generalize h₁ : execInstrBr state (.LD .x5 .x24 (BitVec.ofNat 12 (16+160*k+8*m))) = s₁ at run₁ pc₁ mem₁ x5₁ keep₁
  have value : s₁.getReg .x5 = sourceWord sub input (142*r + 2 + 20*k + m) := by
    rw [x5₁, if_neg (by decide)]
    have e : state.getMem (BitVec.ofNat 64 (8*src)) = memoryView state src := rfl
    rw [e, at_.low src (by simp only [src]; simp <;> omega) (by right; simp only [src]; omega)
      (by right; simp only [src]; omega)]
    unfold sourceWord
    congr 1
    simp only [src]; omega
  obtain ⟨run₂, pc₂, view₂, keep₂⟩ := wrap_store wrap s₁ .x27 .x5 _ _ c₂ pc₁ (RSW + 40*k + m)
    (by rw [keep₁ .x27 (by decide), x27, o₂, ← BitVec.ofNat_add]; apply word_of_bytes; omega) (by omega)
  generalize h₂ : execInstrBr s₁ (.SD .x27 .x5 (BitVec.ofNat 12 (8*m))) = s₂ at run₂ pc₂ view₂ keep₂
  obtain ⟨run₃, pc₃, view₃, keep₃⟩ := wrap_store wrap s₂ .x27 .x5 _ _ c₃ pc₂ (RSW + 40*k + 20 + m)
    (by rw [keep₂, keep₁ .x27 (by decide), x27, o₃, ← BitVec.ofNat_add]; apply word_of_bytes; omega) (by omega)
  generalize h₃ : execInstrBr s₂ (.SD .x27 .x5 (BitVec.ofNat 12 (160+8*m))) = s₃ at run₃ pc₃ view₃ keep₃
  have regs (reg : Reg) (a : reg ≠ .x5) : s₃.getReg reg = state.getReg reg := by
    rw [keep₃, keep₂, keep₁ reg a]
  have stored : s₂.getReg .x5 = sourceWord sub input (142*r + 2 + 20*k + m) := by rw [keep₂, value]
  have view (w : Nat) (hw : w < 2^61) : memoryView s₃ w =
      if w = RSW + 40*k + 20 + m then sourceWord sub input (142*r + 2 + 20*k + m)
      else if w = RSW + 40*k + m then sourceWord sub input (142*r + 2 + 20*k + m) else memoryView state w := by
    rw [view₃ w hw, stored, view₂ w hw, value, view_of_mem mem₁]
  refine ⟨s₃, (run₁.trans (run₂.trans run₃)).cast rfl rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [regs .x24 (by decide), at_.x24]
  · rw [regs .x25 (by decide), at_.x25]
  · rw [regs .x26 (by decide), at_.x26]
  · exact at_.consts.keep (fun reg member => regs reg (by rintro rfl; exact absurd member (by decide)))
  · exact at_.kept.keep (fun reg member => regs reg (by rintro rfl; exact absurd member (by decide)))
  · intro x hx
    rw [view _ (by omega), if_neg (by omega), if_neg (by omega)]
    exact at_.table x hx
  · intro x hx
    rw [view _ (by omega), if_neg (by omega : ¬ x < 0)]
    have old := at_.rs x hx
    rw [if_neg (by omega : ¬ x < 0)] at old
    unfold rsWord at old ⊢
    by_cases a : RSW + x = RSW + 40*k + 20 + m
    · rw [if_pos a, if_pos (by omega)]
      congr 1; omega
    · rw [if_neg a]
      by_cases b : RSW + x = RSW + 40*k + m
      · rw [if_pos b, if_pos (by omega)]
        congr 1; omega
      · rw [if_neg b, old]
        have idx : 20*(x/40) + x%40%20 ≠ 20*k + m := by omega
        by_cases c : 20*(x/40) + x%40%20 < 20*k + m
        · rw [if_pos c, if_pos (by omega)]
        · rw [if_neg c, if_neg (by omega)]
  · intro w hw s₁' s₂'
    have hw' := hw
    simp at hw'
    rw [view _ (by omega), if_neg (by omega), if_neg (by omega)]
    exact at_.low w hw s₁' s₂'
  · intro w lo hi; simp at hi; omega
  · intro w lo hi
    rw [view _ (by omega), if_neg (by omega), if_neg (by omega)]
    exact at_.done w lo hi
  · intro w hw lo
    rw [view _ (by omega), if_neg (by omega), if_neg (by omega)]
    exact at_.high w hw lo
  · rw [regs .x27 (by decide), x27]
  · rw [pc₃]; congr 1

/-- One group (level `k`): 20 doubled doublewords, then `x27 += 320`. -/
theorem dbl_level {sub : Submission} (wrap : WrapImage (sub.image .check)) (input : CheckInput)
    (r k : Nat) (present : r < input.positions.card) (hk : k < 7)
    (state : MachineState) (pc : state.pc = BitVec.ofNat 64 (4096+4*(460+(3471+61*k))))
    (x27 : state.getReg .x27 = BitVec.ofNat 64 (RS + 320*k))
    (at_ : Body sub input r (20*k) 0 0 state) :
    ∃ next : MachineState, Hop (sub.image .check) state next 61 61 ∧ Body sub input r (20*(k+1)) 0 0 next ∧
      next.getReg .x27 = BitVec.ofNat 64 (RS + 320*(k+1)) ∧
      next.pc = BitVec.ofNat 64 (4096+4*(460+(3471+61*(k+1)))) := by
  have loop : ∀ m ≤ 20, ∃ mid : MachineState, Hop (sub.image .check) state mid (3*m) (3*m) ∧
      Body sub input r (20*k+m) 0 0 mid ∧ mid.getReg .x27 = BitVec.ofNat 64 (RS + 320*k) ∧
      mid.pc = BitVec.ofNat 64 (4096+4*(460+(3471+61*k+3*m))) := by
    intro m
    induction m with
    | zero => exact fun _ => ⟨state, Hop.zero _ _, by simpa using at_, x27, by simpa using pc⟩
    | succ m ih =>
      intro le
      obtain ⟨mid, run, atMid, x27Mid, pcMid⟩ := ih (by omega)
      obtain ⟨next, run₂, atNext, x27Next, pcNext⟩ := dbl_step wrap input r k m present hk (by omega) mid pcMid x27Mid atMid
      exact ⟨next, (run.trans run₂).cast (by omega) (by omega), by simpa [Nat.add_assoc] using atNext, x27Next, pcNext⟩
  obtain ⟨mid, run, atMid, x27Mid, pcMid⟩ := loop 20 le_rfl
  obtain ⟨_, _, _, adv, _⟩ := body_codes
  have pure₁ : ([.ADDI .x27 .x27 320] : List Instr).all wrapPure = true := rfl
  have run₁ := wrap_pure_run wrap _ (3471+61*k+60) mid (adv k hk) (by rw [pcMid]) pure₁
  have pc₁ := wrap_pure_pc _ mid pure₁
  have mem₁ := wrap_pure_mem _ mid pure₁
  have x27₁ : (([.ADDI .x27 .x27 320] : List Instr).foldl execInstrBr mid).getReg .x27 =
      mid.getReg .x27 + signExtend12 320 := by simp [execInstrBr, get_reg_set_reg]
  have keep₁ (reg : Reg) (a : reg ≠ .x27) :
      (([.ADDI .x27 .x27 320] : List Instr).foldl execInstrBr mid).getReg reg = mid.getReg reg := by
    simp [execInstrBr, get_reg_set_reg, Ne.symm a]
  refine ⟨_, (run.trans run₁).cast (by simp) (by simp [wrapCost, instructionCycles]),
    Body.keep (show Body sub input r (20*(k+1)) 0 0 mid by rw [show 20*(k+1) = 20*k+20 by ring]; exact atMid) mem₁
      (fun reg n => keep₁ reg (by intro e; subst e; exact n (by decide))), ?_, ?_⟩
  · rw [x27₁, x27Mid, body_offsets.2.2.2.1, ← BitVec.ofNat_add]; congr 1
  · rw [pc₁, pcMid, pc_add]; congr 1

theorem dbl_all {sub : Submission} (wrap : WrapImage (sub.image .check)) (input : CheckInput)
    (r : Nat) (present : r < input.positions.card) :
    ∀ k ≤ 7, ∀ state : MachineState, state.pc = BitVec.ofNat 64 (4096+4*(460+3471)) →
      state.getReg .x27 = BitVec.ofNat 64 RS → Body sub input r 0 0 0 state →
      ∃ next : MachineState, Hop (sub.image .check) state next (61*k) (61*k) ∧ Body sub input r (20*k) 0 0 next ∧
        next.getReg .x27 = BitVec.ofNat 64 (RS + 320*k) ∧
        next.pc = BitVec.ofNat 64 (4096+4*(460+(3471+61*k))) := by
  intro k
  induction k with
  | zero => intro _ state pc x27 at_; exact ⟨state, Hop.zero _ _, at_, by simpa using x27, by simpa using pc⟩
  | succ k ih =>
    intro le state pc x27 at_
    obtain ⟨mid, run, atMid, x27Mid, pcMid⟩ := ih (by omega) state pc x27 at_
    obtain ⟨next, run₂, atNext, x27Next, pcNext⟩ := dbl_level wrap input r k present (by omega) mid pcMid x27Mid atMid
    exact ⟨next, (run.trans run₂).cast (by ring) (by ring), atNext, x27Next, pcNext⟩

/-- The salt, the index and the scratch pointer. -/
theorem salt_run {sub : Submission} (lay : WrapLayout sub) (wrap : WrapImage (sub.image .check))
    (input : CheckInput) (r : Nat) (present : r < input.positions.card)
    (state : MachineState) (pc : state.pc = BitVec.ofNat 64 (4096+4*(460+3898)))
    (at_ : Body sub input r 140 0 0 state) :
    ∃ next : MachineState, Hop (sub.image .check) state next 6 6 ∧ Body sub input r 140 2 0 next ∧
      next.getReg .x6 = BitVec.ofNat 64 (sortedIndex input.positions r) ∧
      next.getReg .x30 = BitVec.ofNat 64 RS ∧
      next.pc = BitVec.ofNat 64 (4096+4*(460+3904)) := by
  have card := card_small input
  have pw : proofWord = 1350566924 := rfl
  have pb : PENTA_PROOF_BASE = 10804535392 := rfl
  have tw : TBW = 33554432 := rfl
  have rw' : RSW = 33562624 := rfl
  have room : MEMORY_BYTES = 68719476736 := rfl
  obtain ⟨_, _, _, _, c₁, c₂, c₃, c₄, c₅, c₆, _⟩ := body_codes
  obtain ⟨_, _, _, _, o8, o0, lui⟩ := body_offsets
  let src (e : Nat) := proofWord + 142*r + e
  have srcLow (e : Nat) (he : e < 2) : memoryView state (src e) = sourceWord sub input (142*r + e) := by
    rw [at_.low (src e) (by simp only [src]; simp <;> omega) (by right; simp only [src]; omega)
      (by right; simp only [src]; omega)]
    unfold sourceWord; congr 1; simp only [src]; omega
  -- word 0
  obtain ⟨run₁, pc₁, mem₁, x5₁, keep₁⟩ := wrap_load wrap state .x5 .x24 _ _ c₁ pc (8*src 0)
    (by rw [at_.x24, o0, BitVec.add_zero]; apply congrArg (BitVec.ofNat 64); simp only [src]; omega) (by omega) (by simp only [src]; omega)
  generalize h₁ : execInstrBr state (.LD .x5 .x24 0) = s₁ at run₁ pc₁ mem₁ x5₁ keep₁
  have v₁ : s₁.getReg .x5 = sourceWord sub input (142*r + 0) := by
    rw [x5₁, if_neg (by decide), ← srcLow 0 (by decide)]; rfl
  obtain ⟨run₂, pc₂, view₂, keep₂⟩ := wrap_store wrap s₁ .x25 .x5 _ _ c₂ pc₁ (proofWord + 178*r)
    (by rw [keep₁ .x25 (by decide), at_.x25, o0, BitVec.add_zero]; apply word_of_bytes; omega) (by omega)
  generalize h₂ : execInstrBr s₁ (.SD .x25 .x5 0) = s₂ at run₂ pc₂ view₂ keep₂
  -- word 1
  have src1 : memoryView s₂ (src 1) = sourceWord sub input (142*r + 1) := by
    rw [view₂ _ (by simp only [src]; omega), if_neg (by simp only [src]; omega), view_of_mem mem₁, srcLow 1 (by decide)]
  obtain ⟨run₃, pc₃, mem₃, x5₃, keep₃⟩ := wrap_load wrap s₂ .x5 .x24 _ _ c₃ pc₂ (8*src 1)
    (by rw [keep₂, keep₁ .x24 (by decide), at_.x24, o8, ← BitVec.ofNat_add]; apply congrArg (BitVec.ofNat 64); simp only [src]; omega)
    (by omega) (by simp only [src]; omega)
  generalize h₃ : execInstrBr s₂ (.LD .x5 .x24 8) = s₃ at run₃ pc₃ mem₃ x5₃ keep₃
  have v₃ : s₃.getReg .x5 = sourceWord sub input (142*r + 1) := by
    rw [x5₃, if_neg (by decide), ← src1]; rfl
  obtain ⟨run₄, pc₄, view₄, keep₄⟩ := wrap_store wrap s₃ .x25 .x5 _ _ c₄ pc₃ (proofWord + 178*r + 1)
    (by rw [keep₃ .x25 (by decide), keep₂, keep₁ .x25 (by decide), at_.x25, o8, ← BitVec.ofNat_add]
        apply word_of_bytes; omega) (by omega)
  generalize h₄ : execInstrBr s₃ (.SD .x25 .x5 8) = s₄ at run₄ pc₄ view₄ keep₄
  -- index
  obtain ⟨run₅, pc₅, mem₅, x6₅, keep₅⟩ := wrap_load wrap s₄ .x6 .x26 0 _ c₅ pc₄ (8*(796918788 + r))
    (by rw [keep₄, keep₃ .x26 (by decide), keep₂, keep₁ .x26 (by decide), at_.x26, o0, BitVec.add_zero]
        congr 1; omega) (by omega) (by omega)
  generalize h₅ : execInstrBr s₄ (.LD .x6 .x26 0) = s₅ at run₅ pc₅ mem₅ x6₅ keep₅
  have view (w : Nat) (hw : w < 2^61) : memoryView s₅ w =
      if w = proofWord + 178*r + 1 then sourceWord sub input (142*r + 1)
      else if w = proofWord + 178*r then sourceWord sub input (142*r + 0) else memoryView state w := by
    rw [view_of_mem mem₅, view₄ w hw, v₃, view_of_mem mem₃, view₂ w hw, v₁, view_of_mem mem₁]
  have idx : s₅.getReg .x6 = BitVec.ofNat 64 (sortedIndex input.positions r) := by
    rw [x6₅, if_neg (by decide)]
    have e : s₄.getMem (BitVec.ofNat 64 (8*(796918788 + r))) = memoryView s₅ (796918788 + r) := by
      rw [view_of_mem mem₅]; rfl
    rw [e, view _ (by omega), if_neg (by omega), if_neg (by omega),
      at_.low _ (by simp <;> omega) (by right; omega) (by right; omega), index_word lay input r present]
  have pure₆ : ([.LUI .x30 65552] : List Instr).all wrapPure = true := rfl
  have run₆ := wrap_pure_run wrap _ 3903 s₅ c₆ (by rw [pc₅]) pure₆
  have pc₆ := wrap_pure_pc _ s₅ pure₆
  have mem₆ := wrap_pure_mem _ s₅ pure₆
  have x30₆ : (([.LUI .x30 65552] : List Instr).foldl execInstrBr s₅).getReg .x30 = BitVec.ofNat 64 RS := by
    simp [execInstrBr, get_reg_set_reg]; exact lui
  have keep₆ (reg : Reg) (a : reg ≠ .x30) :
      (([.LUI .x30 65552] : List Instr).foldl execInstrBr s₅).getReg reg = s₅.getReg reg := by
    simp [execInstrBr, get_reg_set_reg, Ne.symm a]
  generalize h₆ : ([.LUI .x30 65552] : List Instr).foldl execInstrBr s₅ = s₆ at run₆ pc₆ mem₆ x30₆ keep₆
  have regs (reg : Reg) (a : reg ≠ .x5) (b : reg ≠ .x6) (c : reg ≠ .x30) : s₆.getReg reg = state.getReg reg := by
    rw [keep₆ reg c, keep₅ reg b, keep₄, keep₃ reg a, keep₂, keep₁ reg a]
  have view6 (w : Nat) (hw : w < 2^61) := (view_of_mem mem₆ w).trans (view w hw)
  refine ⟨s₆, (run₁.trans (run₂.trans (run₃.trans (run₄.trans (run₅.trans run₆))))).cast rfl
      (by simp [wrapCost, instructionCycles]), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, x30₆, ?_⟩
  · rw [regs .x24 (by decide) (by decide) (by decide), at_.x24]
  · rw [regs .x25 (by decide) (by decide) (by decide), at_.x25]
  · rw [regs .x26 (by decide) (by decide) (by decide), at_.x26]
  · exact at_.consts.keep (fun reg member => regs reg (by rintro rfl; exact absurd member (by decide))
      (by rintro rfl; exact absurd member (by decide)) (by rintro rfl; exact absurd member (by decide)))
  · exact at_.kept.keep (fun reg member => regs reg (by rintro rfl; exact absurd member (by decide))
      (by rintro rfl; exact absurd member (by decide)) (by rintro rfl; exact absurd member (by decide)))
  · intro x hx; rw [view6 _ (by omega), if_neg (by omega), if_neg (by omega)]; exact at_.table x hx
  · intro x hx; rw [view6 _ (by omega), if_neg (by omega), if_neg (by omega)]; exact at_.rs x hx
  · intro w hw s₁' s₂'
    simp at hw
    rw [view6 _ (by omega), if_neg (by omega), if_neg (by omega)]
    exact at_.low w (by simp <;> omega) s₁' s₂'
  · intro w lo hi
    rw [view6 _ (by omega)]
    unfold expandedWord
    by_cases one : w = proofWord + 178*r + 1
    · rw [if_pos one, if_pos (by omega), show (w - proofWord) / 178 = r by omega,
        show (w - proofWord) % 178 = 1 by omega]
    · rw [if_neg one, if_pos (by omega), if_pos (by omega), show (w - proofWord) / 178 = r by omega,
        show (w - proofWord) % 178 = 0 by omega]
  · intro w lo hi; rw [view6 _ (by omega), if_neg (by omega), if_neg (by omega)]; exact at_.done w lo hi
  · intro w hw lo; rw [view6 _ (by omega), if_neg (by omega), if_neg (by omega)]; exact at_.high w hw lo
  · rw [keep₆ .x6 (by decide), idx]
  · rw [pc₆, pc₅, pc_add]; rfl

def rotHead : List Instr :=
  [.DIVU .x7 .x6 .x9, .MUL .x28 .x7 .x9, .SUB .x28 .x6 .x28, .SLLI .x28 .x28 5, .ADD .x29 .x28 .x30]

theorem rot_head_regs (state : MachineState) (q base : Nat) (hq : q < 16777216) (hb : base < 2^40)
    (x6 : state.getReg .x6 = BitVec.ofNat 64 q) (x9 : state.getReg .x9 = BitVec.ofNat 64 5)
    (x30 : state.getReg .x30 = BitVec.ofNat 64 base) :
    (rotHead.foldl execInstrBr state).getReg .x7 = BitVec.ofNat 64 (q/5) ∧
    (rotHead.foldl execInstrBr state).getReg .x29 = BitVec.ofNat 64 (base + 32*(q%5)) ∧
    ∀ r, r ≠ .x7 → r ≠ .x28 → r ≠ .x29 → (rotHead.foldl execInstrBr state).getReg r = state.getReg r := by
  have quot : rv64_divu (BitVec.ofNat 64 q) (BitVec.ofNat 64 5) = BitVec.ofNat 64 (q/5) :=
    divu_value q 5 (by decide) (by omega) (by decide)
  refine ⟨?_, ?_, ?_⟩
  · simp [rotHead, execInstrBr, get_reg_set_reg, x6, x9, quot]
  · simp only [rotHead, List.foldl_cons, List.foldl_nil, execInstrBr, MachineState.getReg_setPC, get_reg_set_reg]
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, and_true, and_false, if_true, if_false, true_and, false_and]
    rw [x6, x9, x30, quot]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_sub, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq]
    have hmod : q / 5 * 5 % 18446744073709551616 = q / 5 * 5 := Nat.mod_eq_of_lt (by omega)
    norm_num
    omega
  · intro r a b c
    simp [rotHead, execInstrBr, get_reg_set_reg, Ne.symm a, Ne.symm b, Ne.symm c]

/-- One rotated doubleword of level `k`. -/
theorem rot_pair {sub : Submission} (wrap : WrapImage (sub.image .check)) (input : CheckInput)
    (r k m : Nat) (present : r < input.positions.card) (hk : k < 7) (hm : m < 16)
    (state : MachineState) (pc : state.pc = BitVec.ofNat 64 (4096+4*(460+(3904+39*k+5+2*m))))
    (x29 : state.getReg .x29 = BitVec.ofNat 64
      (RS + 320*k + 32*capDigit (sortedIndex input.positions r) k))
    (at_ : Body sub input r 140 (2+16*k+m) 0 state) :
    ∃ next : MachineState, Hop (sub.image .check) state next 2 2 ∧ Body sub input r 140 (2+16*k+m+1) 0 next ∧
      (∀ reg, reg ≠ .x31 → next.getReg reg = state.getReg reg) ∧
      next.pc = BitVec.ofNat 64 (4096+4*(460+(3904+39*k+5+2*(m+1)))) := by
  have card := card_small input
  have pw : proofWord = 1350566924 := rfl
  have pb : PENTA_PROOF_BASE = 10804535392 := rfl
  have tw : TBW = 33554432 := rfl
  have rw' : RSW = 33562624 := rfl
  have rsv : RS = 268500992 := rfl
  have room : MEMORY_BYTES = 68719476736 := rfl
  obtain ⟨_, _, _, _, _, _, _, _, _, _, rot, _⟩ := body_codes
  obtain ⟨_, pairs, _⟩ := rot k hk
  obtain ⟨c₁, c₂⟩ := pairs m hm
  obtain ⟨_, roffs, _⟩ := body_offsets
  obtain ⟨o₁, o₂⟩ := roffs k hk m hm
  generalize hd : capDigit (sortedIndex input.positions r) k = d at x29
  have hd5 : d < 5 := by rw [← hd]; unfold capDigit; omega
  let x := 40*k + 4*(d+1) + m
  obtain ⟨run₁, pc₁, mem₁, x31₁, keep₁⟩ := wrap_load wrap state .x31 .x29 _ _ c₁ pc (8*(RSW + x))
    (by rw [x29, o₁, ← BitVec.ofNat_add]; congr 1; simp only [x]; omega) (by omega) (by simp only [x]; omega)
  generalize h₁ : execInstrBr state (.LD .x31 .x29 (BitVec.ofNat 12 (32+8*m))) = s₁ at run₁ pc₁ mem₁ x31₁ keep₁
  have value : s₁.getReg .x31 = expandedWord sub input (178*r + 2 + 16*k + m) := by
    rw [x31₁, if_neg (by decide)]
    have e : state.getMem (BitVec.ofNat 64 (8*(RSW + x))) = memoryView state (RSW + x) := rfl
    rw [e, at_.rs x (by simp only [x]; omega), if_neg (by omega)]
    unfold rsWord expandedWord
    have a₁ : x / 40 = k := by simp only [x]; omega
    have a₂ : x % 40 % 20 = (4*(d+1) + m) % 20 := by simp only [x]; omega
    rw [a₁, a₂, if_pos (by omega)]
    have v₁ : (178*r + 2 + 16*k + m) % 178 = 2 + 16*k + m := by omega
    have v₂ : (178*r + 2 + 16*k + m) / 178 = r := by omega
    rw [v₁, v₂, if_neg (by omega), if_pos (by omega)]
    dsimp only
    rw [show (2 + 16*k + m - 2) / 16 = k by omega, show (2 + 16*k + m - 2) % 16 / 4 = m / 4 by omega,
      show (2 + 16*k + m - 2) % 4 = m % 4 by omega, hd]
    unfold sourceWord
    congr 2
    omega
  let dest := proofWord + 178*r + 2 + 16*k + m
  obtain ⟨run₂, pc₂, view₂, keep₂⟩ := wrap_store wrap s₁ .x25 .x31 _ _ c₂ pc₁ dest
    (by rw [keep₁ .x25 (by decide), at_.x25, o₂, ← BitVec.ofNat_add]; apply word_of_bytes; simp only [dest]; omega)
    (by simp only [dest]; omega)
  generalize h₂ : execInstrBr s₁ (.SD .x25 .x31 (BitVec.ofNat 12 (16+128*k+8*m))) = s₂ at run₂ pc₂ view₂ keep₂
  have regs (reg : Reg) (a : reg ≠ .x31) : s₂.getReg reg = state.getReg reg := by rw [keep₂, keep₁ reg a]
  have view (w : Nat) (hw : w < 2^61) : memoryView s₂ w =
      if w = dest then expandedWord sub input (178*r + 2 + 16*k + m) else memoryView state w := by
    rw [view₂ w hw, value, view_of_mem mem₁]
  refine ⟨s₂, (run₁.trans run₂).cast rfl rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, regs, ?_⟩
  · rw [regs .x24 (by decide), at_.x24]
  · rw [regs .x25 (by decide), at_.x25]
  · rw [regs .x26 (by decide), at_.x26]
  · exact at_.consts.keep (fun reg member => regs reg (by rintro rfl; exact absurd member (by decide)))
  · exact at_.kept.keep (fun reg member => regs reg (by rintro rfl; exact absurd member (by decide)))
  · intro y hy; rw [view _ (by omega), if_neg (by simp only [dest]; omega)]; exact at_.table y hy
  · intro y hy; rw [view _ (by omega), if_neg (by simp only [dest]; omega)]; exact at_.rs y hy
  · intro w hw s₁' s₂'
    rw [if_neg (by omega)] at hw
    rw [view _ (by omega), if_neg (by simp only [dest]; omega)]
    exact at_.low w (by rw [if_neg (by omega)]; omega) s₁' s₂'
  · intro w lo hi
    rw [view _ (by omega)]
    by_cases here : w = dest
    · rw [if_pos here, show w - proofWord = 178*r + 2 + 16*k + m by simp only [dest] at here; omega]
    · rw [if_neg here]; exact at_.filled w lo (by simp only [dest] at here; omega)
  · intro w lo hi; rw [view _ (by omega), if_neg (by simp only [dest]; omega)]; exact at_.done w lo hi
  · intro w hw lo; rw [view _ (by omega), if_neg (by simp only [dest]; omega)]; exact at_.high w hw lo
  · rw [pc₂]; congr 1

/-- Level `k ≤ 6` of the expanded record. -/
theorem rot_level {sub : Submission} (wrap : WrapImage (sub.image .check)) (input : CheckInput)
    (r k : Nat) (present : r < input.positions.card) (hk : k < 7)
    (state : MachineState) (pc : state.pc = BitVec.ofNat 64 (4096+4*(460+(3904+39*k))))
    (x6 : state.getReg .x6 = BitVec.ofNat 64 (sortedIndex input.positions r / 5^k))
    (x30 : state.getReg .x30 = BitVec.ofNat 64 (RS + 320*k))
    (at_ : Body sub input r 140 (2+16*k) 0 state) :
    ∃ next : MachineState, Hop (sub.image .check) state next 39 45 ∧ Body sub input r 140 (2+16*(k+1)) 0 next ∧
      next.getReg .x6 = BitVec.ofNat 64 (sortedIndex input.positions r / 5^(k+1)) ∧
      next.getReg .x30 = BitVec.ofNat 64 (RS + 320*(k+1)) ∧
      next.pc = BitVec.ofNat 64 (4096+4*(460+(3904+39*(k+1)))) := by
  have rsv : RS = 268500992 := rfl
  obtain ⟨_, _, _, _, _, _, _, _, _, _, rot, _⟩ := body_codes
  obtain ⟨c₁, _, c₃⟩ := rot k hk
  have small := sorted_index_small input.positions r
  have q : sortedIndex input.positions r / 5^k < 16777216 := lt_of_le_of_lt (Nat.div_le_self _ _) small
  have pure₁ : rotHead.all wrapPure = true := by unfold rotHead; simp [wrapPure]
  have run₁ := wrap_pure_run wrap rotHead (3904+39*k) state c₁ pc pure₁
  have pc₁ := wrap_pure_pc rotHead state pure₁
  have mem₁ := wrap_pure_mem rotHead state pure₁
  obtain ⟨x7₁, x29₁, keep₁⟩ := rot_head_regs state _ (RS + 320*k) q (by omega) x6 at_.consts.five x30
  generalize h₁ : rotHead.foldl execInstrBr state = s₁ at run₁ pc₁ mem₁ x7₁ x29₁ keep₁
  have at₁ : Body sub input r 140 (2+16*k+0) 0 s₁ :=
    at_.keep mem₁ (fun reg n => keep₁ reg (by intro e; subst e; exact n (by decide))
      (by intro e; subst e; exact n (by decide)) (by intro e; subst e; exact n (by decide)))
  have digit : RS + 320*k + 32*(sortedIndex input.positions r / 5^k % 5) =
      RS + 320*k + 32*capDigit (sortedIndex input.positions r) k := rfl
  have loop : ∀ m ≤ 16, ∃ mid : MachineState, Hop (sub.image .check) s₁ mid (2*m) (2*m) ∧
      Body sub input r 140 (2+16*k+m) 0 mid ∧ (∀ reg, reg ≠ .x31 → mid.getReg reg = s₁.getReg reg) ∧
      mid.pc = BitVec.ofNat 64 (4096+4*(460+(3904+39*k+5+2*m))) := by
    intro m
    induction m with
    | zero =>
      intro _
      exact ⟨s₁, Hop.zero _ _, at₁, fun _ _ => rfl, by rw [pc₁, pc, pc_add]; rfl⟩
    | succ m ih =>
      intro le
      obtain ⟨mid, run, atMid, regMid, pcMid⟩ := ih (by omega)
      obtain ⟨next, run₂, atNext, regNext, pcNext⟩ := rot_pair wrap input r k m present hk (by omega) mid pcMid
        (by rw [regMid .x29 (by decide), x29₁, digit]) atMid
      exact ⟨next, (run.trans run₂).cast (by omega) (by omega), atNext,
        fun reg a => (regNext reg a).trans (regMid reg a), pcNext⟩
  obtain ⟨s₂, run₂, at₂, reg₂, pc₂⟩ := loop 16 le_rfl
  have pure₃ : ([.ADDI .x6 .x7 0, .ADDI .x30 .x30 320] : List Instr).all wrapPure = true := rfl
  have run₃ := wrap_pure_run wrap _ (3904+39*k+37) s₂ c₃ (by rw [pc₂]) pure₃
  have pc₃ := wrap_pure_pc _ s₂ pure₃
  have mem₃ := wrap_pure_mem _ s₂ pure₃
  have x6₃ : (([.ADDI .x6 .x7 0, .ADDI .x30 .x30 320] : List Instr).foldl execInstrBr s₂).getReg .x6 =
      s₂.getReg .x7 + signExtend12 0 := by simp [execInstrBr, get_reg_set_reg]
  have x30₃ : (([.ADDI .x6 .x7 0, .ADDI .x30 .x30 320] : List Instr).foldl execInstrBr s₂).getReg .x30 =
      s₂.getReg .x30 + signExtend12 320 := by simp [execInstrBr, get_reg_set_reg]
  have keep₃ (reg : Reg) (a : reg ≠ .x6) (b : reg ≠ .x30) :
      (([.ADDI .x6 .x7 0, .ADDI .x30 .x30 320] : List Instr).foldl execInstrBr s₂).getReg reg = s₂.getReg reg := by
    simp [execInstrBr, get_reg_set_reg, Ne.symm a, Ne.symm b]
  obtain ⟨_, _, _, s320, _, s0, _⟩ := body_offsets
  refine ⟨_, ((run₁.trans run₂).trans run₃).cast (by unfold rotHead; simp)
      (by unfold rotHead; simp [wrapCost, instructionCycles]),
    Body.keep (show Body sub input r 140 (2+16*(k+1)) 0 s₂ by rw [show 2+16*(k+1) = 2+16*k+16 by ring]; exact at₂) mem₃
      (fun reg n => keep₃ reg (by intro e; subst e; exact n (by decide)) (by intro e; subst e; exact n (by decide))),
    ?_, ?_, ?_⟩
  · rw [x6₃, reg₂ .x7 (by decide), x7₁, s0, BitVec.add_zero, pow_succ, ← Nat.div_div_eq_div_mul]
  · rw [x30₃, reg₂ .x30 (by decide), keep₁ .x30 (by decide) (by decide) (by decide), x30, s320,
      ← BitVec.ofNat_add]; congr 1
  · rw [pc₃, pc₂, pc_add]; congr 1

theorem rot_all {sub : Submission} (wrap : WrapImage (sub.image .check)) (input : CheckInput)
    (r : Nat) (present : r < input.positions.card) :
    ∀ k ≤ 7, ∀ state : MachineState, state.pc = BitVec.ofNat 64 (4096+4*(460+3904)) →
      state.getReg .x6 = BitVec.ofNat 64 (sortedIndex input.positions r) →
      state.getReg .x30 = BitVec.ofNat 64 RS → Body sub input r 140 2 0 state →
      ∃ next : MachineState, Hop (sub.image .check) state next (39*k) (45*k) ∧
        Body sub input r 140 (2+16*k) 0 next ∧
        next.getReg .x6 = BitVec.ofNat 64 (sortedIndex input.positions r / 5^k) ∧
        next.getReg .x30 = BitVec.ofNat 64 (RS + 320*k) ∧
        next.pc = BitVec.ofNat 64 (4096+4*(460+(3904+39*k))) := by
  intro k
  induction k with
  | zero => intro _ state pc x6 x30 at_; exact ⟨state, Hop.zero _ _, at_, by simpa using x6, by simpa using x30,
      by simpa using pc⟩
  | succ k ih =>
    intro le state pc x6 x30 at_
    obtain ⟨mid, run, atMid, x6Mid, x30Mid, pcMid⟩ := ih (by omega) state pc x6 x30 at_
    obtain ⟨next, run₂, atNext, x6Next, x30Next, pcNext⟩ :=
      rot_level wrap input r k present (by omega) mid pcMid x6Mid x30Mid atMid
    exact ⟨next, (run.trans run₂).cast (by ring) (by ring), atNext, x6Next, x30Next, pcNext⟩

theorem clr_step {sub : Submission} (wrap : WrapImage (sub.image .check)) (input : CheckInput)
    (r k m : Nat) (present : r < input.positions.card) (hk : k < 7) (hm : m < 40)
    (state : MachineState) (pc : state.pc = BitVec.ofNat 64 (4096+4*(460+(4178+41*k+m))))
    (x27 : state.getReg .x27 = BitVec.ofNat 64 (RS + 320*k))
    (at_ : Body sub input r 140 114 (40*k+m) state) :
    ∃ next : MachineState, Hop (sub.image .check) state next 1 1 ∧ Body sub input r 140 114 (40*k+m+1) next ∧
      next.getReg .x27 = BitVec.ofNat 64 (RS + 320*k) ∧
      next.pc = BitVec.ofNat 64 (4096+4*(460+(4178+41*k+(m+1)))) := by
  have rw' : RSW = 33562624 := rfl
  have rsv : RS = 268500992 := rfl
  have tw : TBW = 33554432 := rfl
  have pw : proofWord = 1350566924 := rfl
  have room : MEMORY_BYTES = 68719476736 := rfl
  have card := card_small input
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, clr, _⟩ := body_codes
  obtain ⟨c₁, _⟩ := clr k hk
  obtain ⟨_, _, coffs, _⟩ := body_offsets
  obtain ⟨run, pc₁, view, keep⟩ := wrap_store wrap state .x27 .x0 _ _ (c₁ m hm) pc (RSW + 40*k + m)
    (by rw [x27, coffs m hm, ← BitVec.ofNat_add]; apply word_of_bytes; omega) (by omega)
  have zero : state.getReg .x0 = 0 := rfl
  rw [zero] at view
  refine ⟨_, run, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by rw [keep, x27], by rw [pc₁]; congr 1⟩
  · rw [keep, at_.x24]
  · rw [keep, at_.x25]
  · rw [keep, at_.x26]
  · exact at_.consts.keep (fun reg _ => keep reg)
  · exact at_.kept.keep (fun reg _ => keep reg)
  · intro x hx; rw [view _ (by omega), if_neg (by omega)]; exact at_.table x hx
  · intro x hx
    rw [view _ (by omega)]
    by_cases here : RSW + x = RSW + 40*k + m
    · rw [if_pos here, if_pos (by omega)]
    · rw [if_neg here, at_.rs x hx]
      by_cases c : x < 40*k+m
      · rw [if_pos c, if_pos (by omega)]
      · rw [if_neg c, if_neg (by omega)]
  · intro w hw s₁ s₂
    have hw' := hw
    simp at hw'
    rw [view _ (by omega), if_neg (by omega)]; exact at_.low w hw s₁ s₂
  · intro w lo hi; rw [view _ (by omega), if_neg (by omega)]; exact at_.filled w lo hi
  · intro w lo hi; rw [view _ (by omega), if_neg (by omega)]; exact at_.done w lo hi
  · intro w hw lo; rw [view _ (by omega), if_neg (by omega)]; exact at_.high w hw lo

theorem clr_level {sub : Submission} (wrap : WrapImage (sub.image .check)) (input : CheckInput)
    (r k : Nat) (present : r < input.positions.card) (hk : k < 7)
    (state : MachineState) (pc : state.pc = BitVec.ofNat 64 (4096+4*(460+(4178+41*k))))
    (x27 : state.getReg .x27 = BitVec.ofNat 64 (RS + 320*k))
    (at_ : Body sub input r 140 114 (40*k) state) :
    ∃ next : MachineState, Hop (sub.image .check) state next 41 41 ∧ Body sub input r 140 114 (40*(k+1)) next ∧
      next.getReg .x27 = BitVec.ofNat 64 (RS + 320*(k+1)) ∧
      next.pc = BitVec.ofNat 64 (4096+4*(460+(4178+41*(k+1)))) := by
  have loop : ∀ m ≤ 40, ∃ mid : MachineState, Hop (sub.image .check) state mid m m ∧
      Body sub input r 140 114 (40*k+m) mid ∧ mid.getReg .x27 = BitVec.ofNat 64 (RS + 320*k) ∧
      mid.pc = BitVec.ofNat 64 (4096+4*(460+(4178+41*k+m))) := by
    intro m
    induction m with
    | zero => exact fun _ => ⟨state, Hop.zero _ _, by simpa using at_, x27, by simpa using pc⟩
    | succ m ih =>
      intro le
      obtain ⟨mid, run, atMid, x27Mid, pcMid⟩ := ih (by omega)
      obtain ⟨next, run₂, atNext, x27Next, pcNext⟩ := clr_step wrap input r k m present hk (by omega) mid pcMid x27Mid atMid
      exact ⟨next, (run.trans run₂).cast (by omega) (by omega), by simpa [Nat.add_assoc] using atNext, x27Next, pcNext⟩
  obtain ⟨mid, run, atMid, x27Mid, pcMid⟩ := loop 40 le_rfl
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, clr, _⟩ := body_codes
  obtain ⟨_, adv⟩ := clr k hk
  have pure₁ : ([.ADDI .x27 .x27 320] : List Instr).all wrapPure = true := rfl
  have run₁ := wrap_pure_run wrap _ (4178+41*k+40) mid adv (by rw [pcMid]) pure₁
  have pc₁ := wrap_pure_pc _ mid pure₁
  have mem₁ := wrap_pure_mem _ mid pure₁
  have x27₁ : (([.ADDI .x27 .x27 320] : List Instr).foldl execInstrBr mid).getReg .x27 =
      mid.getReg .x27 + signExtend12 320 := by simp [execInstrBr, get_reg_set_reg]
  have keep₁ (reg : Reg) (a : reg ≠ .x27) :
      (([.ADDI .x27 .x27 320] : List Instr).foldl execInstrBr mid).getReg reg = mid.getReg reg := by
    simp [execInstrBr, get_reg_set_reg, Ne.symm a]
  refine ⟨_, (run.trans run₁).cast (by simp) (by simp [wrapCost, instructionCycles]),
    Body.keep (show Body sub input r 140 114 (40*(k+1)) mid by rw [show 40*(k+1) = 40*k+40 by ring]; exact atMid) mem₁
      (fun reg n => keep₁ reg (by intro e; subst e; exact n (by decide))),
    ?_, ?_⟩
  · rw [x27₁, x27Mid, body_offsets.2.2.2.1, ← BitVec.ofNat_add]; congr 1
  · rw [pc₁, pcMid, pc_add]; congr 1

theorem clr_all {sub : Submission} (wrap : WrapImage (sub.image .check)) (input : CheckInput) (r : Nat)
    (present : r < input.positions.card) :
    ∀ k ≤ 7, ∀ state : MachineState, state.pc = BitVec.ofNat 64 (4096+4*(460+4178)) →
      state.getReg .x27 = BitVec.ofNat 64 RS → Body sub input r 140 114 0 state →
      ∃ next : MachineState, Hop (sub.image .check) state next (41*k) (41*k) ∧ Body sub input r 140 114 (40*k) next ∧
        next.getReg .x27 = BitVec.ofNat 64 (RS + 320*k) ∧
        next.pc = BitVec.ofNat 64 (4096+4*(460+(4178+41*k))) := by
  intro k
  induction k with
  | zero => intro _ state pc x27 at_; exact ⟨state, Hop.zero _ _, at_, by simpa using x27, by simpa using pc⟩
  | succ k ih =>
    intro le state pc x27 at_
    obtain ⟨mid, run, atMid, x27Mid, pcMid⟩ := ih (by omega) state pc x27 at_
    obtain ⟨next, run₂, atNext, x27Next, pcNext⟩ := clr_level wrap input r k present (by omega) mid pcMid x27Mid atMid
    exact ⟨next, (run.trans run₂).cast (by ring) (by ring), atNext, x27Next, pcNext⟩

private theorem lui_rs (state : MachineState) :
    (([.LUI .x27 65552] : List Instr).foldl execInstrBr state).getReg .x27 = BitVec.ofNat 64 RS ∧
    ∀ reg, reg ≠ .x27 → (([.LUI .x27 65552] : List Instr).foldl execInstrBr state).getReg reg = state.getReg reg := by
  obtain ⟨_, _, _, _, _, _, lui⟩ := body_offsets
  refine ⟨?_, fun reg a => ?_⟩
  · simp [execInstrBr, get_reg_set_reg]; exact lui
  · simp [execInstrBr, get_reg_set_reg, Ne.symm a]

theorem jal_keeps0 (state : MachineState) (imm : BitVec 21) :
    (execInstrBr state (.JAL .x0 imm)).mem = state.mem ∧ ∀ r, (execInstrBr state (.JAL .x0 imm)).getReg r = state.getReg r :=
  ⟨rfl, fun _ => rfl⟩

/-- The whole record body, from offset 3470 back to offset 122. -/
theorem body_run {sub : Submission} (lay : WrapLayout sub) (wrap : WrapImage (sub.image .check))
    (input : CheckInput) (r : Nat) (present : r < input.positions.card)
    (state : MachineState) (pc : state.pc = BitVec.ofNat 64 (4096+4*(460+3470)))
    (at_ : Body sub input r 0 0 0 state) :
    ∃ next : MachineState, Hop (sub.image .check) state next 996 1038 ∧ Body sub input r 140 114 280 next ∧
      next.pc = BitVec.ofNat 64 (4096+4*(460+122)) := by
  obtain ⟨_, c₀, _, _, _, _, _, _, _, _, _, c₂, _, cj⟩ := body_codes
  have pure₀ : ([.LUI .x27 65552] : List Instr).all wrapPure = true := rfl
  have run₀ := wrap_pure_run wrap _ 3470 state c₀ pc pure₀
  have pc₀ := wrap_pure_pc _ state pure₀
  have mem₀ := wrap_pure_mem _ state pure₀
  obtain ⟨x27₀, keep₀⟩ := lui_rs state
  have at₀ := at_.keep mem₀ (fun reg n => keep₀ reg (by intro e; subst e; exact n (by decide)))
  obtain ⟨s₁, run₁, at₁, _, pc₁⟩ := dbl_all wrap input r present 7 le_rfl _ (by rw [pc₀, pc, pc_add]; rfl) x27₀ at₀
  obtain ⟨s₂, run₂, at₂, x6₂, x30₂, pc₂⟩ := salt_run lay wrap input r present s₁ (by rw [pc₁]) at₁
  obtain ⟨s₃, run₃, at₃, _, _, pc₃⟩ := rot_all wrap input r present 7 le_rfl s₂ pc₂ x6₂ x30₂ at₂
  have run₄ := wrap_pure_run wrap _ 4177 s₃ c₂ (by rw [pc₃]) pure₀
  have pc₄ := wrap_pure_pc _ s₃ pure₀
  have mem₄ := wrap_pure_mem _ s₃ pure₀
  obtain ⟨x27₄, keep₄⟩ := lui_rs s₃
  have at₄ := at₃.keep mem₄ (fun reg n => keep₄ reg (by intro e; subst e; exact n (by decide)))
  obtain ⟨s₅, run₅, at₅, _, pc₅⟩ := clr_all wrap input r present 7 le_rfl _ (by rw [pc₄, pc₃, pc_add]; rfl) x27₄ at₄
  have run₆ := wrap_control wrap s₅ (.JAL .x0 2079780) 4465 cj (by rw [pc₅]) rfl rfl
  obtain ⟨jmem, jregs⟩ := jal_keeps0 s₅ (2079780 : BitVec 21)
  refine ⟨_, (run₀.trans (run₁.trans (run₂.trans (run₃.trans (run₄.trans (run₅.trans run₆)))))).cast rfl
    (by simp [wrapCost, instructionCycles]), at₅.keep jmem (fun reg _ => jregs reg), ?_⟩
  change s₅.pc + signExtend21 2079780 = _
  rw [pc₅]; decide


theorem neg_imm (a c : Nat) (imm : BitVec 12) (h : c ≤ a) (small : a < 2^64)
    (himm : signExtend12 imm = BitVec.ofNat 64 (2^64 - c)) :
    BitVec.ofNat 64 a + signExtend12 imm = BitVec.ofNat 64 (a - c) := by
  rw [himm, ← BitVec.ofNat_add]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
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

theorem latch_code : WrapAt 284 [.ADDI .x24 .x24 2960, .ADDI .x25 .x25 2672, .ADDI .x26 .x26 4088] ∧
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
  have pure₁ : ([.ADDI .x24 .x24 2960, .ADDI .x25 .x25 2672, .ADDI .x26 .x26 4088] : List Instr).all wrapPure = true := rfl
  have run₁ := wrap_pure_run wrap _ 284 state c₁ pc pure₁
  have pc₁ := wrap_pure_pc _ state pure₁
  have mem₁ := wrap_pure_mem _ state pure₁
  have x24₁ : (([.ADDI .x24 .x24 2960, .ADDI .x25 .x25 2672, .ADDI .x26 .x26 4088] : List Instr).foldl execInstrBr state).getReg .x24 =
      state.getReg .x24 + signExtend12 2960 := by simp [execInstrBr, get_reg_set_reg]
  have x25₁ : (([.ADDI .x24 .x24 2960, .ADDI .x25 .x25 2672, .ADDI .x26 .x26 4088] : List Instr).foldl execInstrBr state).getReg .x25 =
      state.getReg .x25 + signExtend12 2672 := by simp [execInstrBr, get_reg_set_reg]
  have x26₁ : (([.ADDI .x24 .x24 2960, .ADDI .x25 .x25 2672, .ADDI .x26 .x26 4088] : List Instr).foldl execInstrBr state).getReg .x26 =
      state.getReg .x26 + signExtend12 4088 := by simp [execInstrBr, get_reg_set_reg]
  have keep₁ (reg : Reg) (a : reg ≠ .x24) (b : reg ≠ .x25) (c : reg ≠ .x26) :
      (([.ADDI .x24 .x24 2960, .ADDI .x25 .x25 2672, .ADDI .x26 .x26 4088] : List Instr).foldl execInstrBr state).getReg reg =
        state.getReg reg := by
    simp [execInstrBr, get_reg_set_reg, Ne.symm a, Ne.symm b, Ne.symm c]
  generalize h₁ : ([.ADDI .x24 .x24 2960, .ADDI .x25 .x25 2672, .ADDI .x26 .x26 4088] : List Instr).foldl execInstrBr state = s₁
    at run₁ pc₁ mem₁ x24₁ x25₁ x26₁ keep₁
  have p24 : s₁.getReg .x24 = BitVec.ofNat 64 (PENTA_PROOF_BASE + 1136*r - 1136) := by
    rw [x24₁, at_.x24, neg_imm _ 1136 2960 (by omega) (by omega) (by decide)]
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


/-- One whole record. -/
theorem record_step {sub : Submission} (lay : WrapLayout sub) (wrap : WrapImage (sub.image .check))
    (input : CheckInput) (r : Nat) (present : r < input.positions.card)
    (state : MachineState) (pc : state.pc = BitVec.ofNat 64 (4096+4*(460+115)))
    (at_ : Expanding sub input (r+1) state) :
    ∃ next : MachineState, Hop (sub.image .check) state next 1163 1244 ∧ Expanding sub input r next ∧
      next.pc = BitVec.ofNat 64 (4096+4*(460+(if r = 0 then 288 else 115))) := by
  have pw : proofWord = 1350566924 := rfl
  have tw : TBW = 33554432 := rfl
  have rw' : RSW = 33562624 := rfl
  obtain ⟨cj, _⟩ := body_codes
  have run₀ := wrap_control wrap state (.JAL .x0 13420) 115 cj pc rfl rfl
  have pc₀ : (execInstrBr state (.JAL .x0 13420)).pc = BitVec.ofNat 64 (4096+4*(460+3470)) := by
    change state.pc + signExtend21 13420 = _
    rw [pc]; decide
  generalize h₀ : execInstrBr state (.JAL .x0 13420) = s₀ at run₀ pc₀
  have mem₀ : s₀.mem = state.mem := by rw [← h₀]; rfl
  have regs₀ (reg : Reg) : s₀.getReg reg = state.getReg reg := by rw [← h₀]; rfl
  have body₀ : Body sub input r 0 0 0 s₀ := by
    refine ⟨?_, ?_, ?_, at_.consts.keep (fun reg _ => regs₀ reg), at_.kept.keep (fun reg _ => regs₀ reg),
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [regs₀, at_.x24]; congr 1
    · rw [regs₀, at_.x25]; congr 1
    · rw [regs₀, at_.x26]; congr 1
    · intro x hx; rw [view_of_mem mem₀]; exact at_.table x hx
    · intro x hx
      rw [view_of_mem mem₀, at_.low _ (by omega) (by right; omega), rs_loader_zero lay input _ (by omega),
        if_neg (by omega)]
      unfold rsWord; rw [if_neg (by omega)]
    · intro w hw side _; simp at hw; rw [view_of_mem mem₀]; exact at_.low w (by omega) side
    · intro w lo hi; omega
    · intro w lo hi; rw [view_of_mem mem₀]; exact at_.done w (by omega) hi
    · intro w hw lo; rw [view_of_mem mem₀]; exact at_.high w hw lo
  obtain ⟨s₁, run₁, at₁, pc₁⟩ := body_run lay wrap input r present s₀ pc₀ body₀
  have copying : Copying sub input r 0 s₁ := by
    refine ⟨at₁.x24, at₁.x25, at₁.x26, at₁.consts, at₁.kept, at₁.table, ?_, ?_, at₁.done, at₁.high⟩
    · intro w hw side
      by_cases scratch : RSW ≤ w ∧ w < RSW + 280
      · obtain ⟨x, rfl⟩ : ∃ x, w = RSW + x := ⟨w - RSW, by omega⟩
        rw [at₁.rs x (by omega), if_pos (by omega), rs_loader_zero lay input _ (by omega)]
      · exact at₁.low w (by simp <;> omega) side (by omega)
    · intro w lo hi; exact at₁.filled w (by omega) hi
  obtain ⟨s₃, run₃, at₃, pc₃⟩ := record_head lay wrap input r present s₁ pc₁ copying
  obtain ⟨s₄, run₄, at₄, pc₄⟩ := record_fills wrap input r present 4 le_rfl s₃ pc₃ at₃
  obtain ⟨s₅, run₅, at₅, pc₅⟩ := record_latch lay wrap input r present s₄ pc₄ at₄
  exact ⟨s₅, (run₀.trans (run₁.trans (run₃.trans (run₄.trans run₅)))).cast (by simp) (by simp), at₅, pc₅⟩

/-- All records, from the last one down. -/
theorem records_loop {sub : Submission} (lay : WrapLayout sub) (wrap : WrapImage (sub.image .check))
    (input : CheckInput) :
    ∀ j ≤ input.positions.card, ∀ state : MachineState, input.positions.card ≠ 0 →
      state.pc = BitVec.ofNat 64 (4096+4*(460+115)) → Expanding sub input input.positions.card state →
      ∃ next : MachineState, Hop (sub.image .check) state next (1163*j) (1244*j) ∧
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
