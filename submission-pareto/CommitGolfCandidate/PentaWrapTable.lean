import CommitGolfCandidate.PentaWrapLoader

/-! The checker wrapper's table phase (wrapper offsets 10-93): each of the 55 table groups of the
cap proof (20 doublewords) is copied twice into scratch memory at `TABLE`, once at `+0` and once
at `+160` of a 320-byte doubled group, and cleared at its source. Afterwards scratch word
`TBW + x` holds `tableWord x`, the cap proof's table area is zero, and every other word is the
loader's. -/

namespace TwoPermutationPrototype.PentaWrap
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.RV64 (memoryView wordAddress)

set_option maxRecDepth 100000

/-- First word of the doubled table (`TABLE / 8`). -/
def TBW : Nat := 33554432

theorem table_value : TABLE = 8*TBW := rfl

/-- Doubled-table word `x`: doubleword `(x % 40) % 20` of table group `x / 40` of the cap proof. -/
def tableWord (sub : Submission) (input : CheckInput) (x : Nat) : Word :=
  sourceWord sub input (114*input.positions.card + 20*(x/40) + (x%40)%20)

/-- Registers the wrapper never writes: `ra sp gp tp a0-a7` (`a7` only at the restore). -/
def keptRegs : List Reg := [.x1, .x2, .x3, .x4, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17]

def Kept (init state : MachineState) : Prop := ∀ r ∈ keptRegs, state.getReg r = init.getReg r

theorem view_of_mem {a b : MachineState} (h : a.mem = b.mem) (w : Nat) : memoryView a w = memoryView b w := by
  unfold memoryView MachineState.getMem
  rw [h]

theorem set_pc_mem (state : MachineState) (pc : Word) : (state.setPC pc).mem = state.mem := rfl
theorem set_pc_reg (state : MachineState) (pc : Word) (r : Reg) : (state.setPC pc).getReg r = state.getReg r := rfl
theorem set_pc_pc (state : MachineState) (pc : Word) : (state.setPC pc).pc = pc := rfl

theorem word_of_bytes (a w : Nat) (h : a = 8*w) : BitVec.ofNat 64 a = wordAddress w := by
  rw [h]; rfl

/-- Table phase after `g` groups. -/
structure TableAt (sub : Submission) (input : CheckInput) (N g : Nat) (state : MachineState) : Prop where
  x6 : state.getReg .x6 = BitVec.ofNat 64 (PENTA_PROOF_BASE + 912*input.positions.card + 160*g)
  x7 : state.getReg .x7 = BitVec.ofNat 64 (TABLE + 320*g)
  x28 : state.getReg .x28 = BitVec.ofNat 64 (N - g)
  kept : Kept (sub.initialState .check input) state
  table : ∀ x < 40*g, memoryView state (TBW + x) = tableWord sub input x
  cleared : ∀ f < 20*g, memoryView state (proofWord + 114*input.positions.card + f) = 0
  rest : ∀ w < 2^33, (w < TBW ∨ TBW + 40*g ≤ w) →
    (w < proofWord + 114*input.positions.card ∨ proofWord + 114*input.positions.card + 20*g ≤ w) →
    memoryView state w = memoryView (sub.initialState .check input) w

/-- Inside group `g` after `m` doublewords. -/
structure GroupAt (sub : Submission) (input : CheckInput) (N g m : Nat) (state : MachineState) : Prop where
  x6 : state.getReg .x6 = BitVec.ofNat 64 (PENTA_PROOF_BASE + 912*input.positions.card + 160*g)
  x7 : state.getReg .x7 = BitVec.ofNat 64 (TABLE + 320*g)
  x28 : state.getReg .x28 = BitVec.ofNat 64 (N - g)
  kept : Kept (sub.initialState .check input) state
  table : ∀ x, (x < 40*g ∨ (40*g ≤ x ∧ x < 40*g + m) ∨ (40*g + 20 ≤ x ∧ x < 40*g + 20 + m)) →
    memoryView state (TBW + x) = tableWord sub input x
  cleared : ∀ f < 20*g + m, memoryView state (proofWord + 114*input.positions.card + f) = 0
  rest : ∀ w < 2^33, (w < TBW ∨ TBW + 40*g + 40 ≤ w ∨
      (TBW + 40*g + m ≤ w ∧ w < TBW + 40*g + 20) ∨ (TBW + 40*g + 20 + m ≤ w ∧ w < TBW + 40*g + 40)) →
    (w < proofWord + 114*input.positions.card ∨ proofWord + 114*input.positions.card + 20*g + m ≤ w) →
    memoryView state w = memoryView (sub.initialState .check input) w

private theorem small_offsets : ∀ m < 20,
    signExtend12 (BitVec.ofNat 12 (8*m)) = BitVec.ofNat 64 (8*m) ∧
    signExtend12 (BitVec.ofNat 12 (160+8*m)) = BitVec.ofNat 64 (160+8*m) := by
  decide

theorem table_group_code : ∀ m < 20,
    wrapCode[10+4*m]? = some (.LD .x5 .x6 (BitVec.ofNat 12 (8*m))) ∧
    wrapCode[10+4*m+1]? = some (.SD .x7 .x5 (BitVec.ofNat 12 (8*m))) ∧
    wrapCode[10+4*m+2]? = some (.SD .x7 .x5 (BitVec.ofNat 12 (160+8*m))) ∧
    wrapCode[10+4*m+3]? = some (.SD .x6 .x0 (BitVec.ofNat 12 (8*m))) := by
  decide +kernel

/-- One doubleword of the table copy. -/
theorem table_step {sub : Submission} (lay : WrapLayout sub) (wrap : WrapImage (sub.image .check))
    (input : CheckInput) (N : Nat) (hN : N ≤ 55)
    (nonempty : input.positions.card ≠ 0) (g m : Nat) (hg : g < N) (hm : m < 20)
    (state : MachineState) (pc : state.pc = BitVec.ofNat 64 (4096+4*(460+(10+4*m))))
    (at_ : GroupAt sub input N g m state) :
    ∃ next : MachineState, Hop (sub.image .check) state next 4 4 ∧ GroupAt sub input N g (m+1) next ∧
      next.pc = BitVec.ofNat 64 (4096+4*(460+(10+4*(m+1)))) := by
  have card : input.positions.card ≤ 16777216 := by
    have : input.positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
    exact this
  have pw : proofWord = 1350566924 := rfl
  have pb : PENTA_PROOF_BASE = 10804535392 := rfl
  have tb : TABLE = 268435456 := rfl
  have tw : TBW = 33554432 := rfl
  have room : MEMORY_BYTES = 68719476736 := rfl
  obtain ⟨c₁, c₂, c₃, c₄⟩ := table_group_code m hm
  obtain ⟨o₁, o₂⟩ := small_offsets m hm
  let k := input.positions.card
  let src := proofWord + 114*k + 20*g + m
  -- load
  obtain ⟨run₁, pc₁, mem₁, x5₁, keep₁⟩ := wrap_load wrap state .x5 .x6 _ (10+4*m) c₁ pc (8*src)
    (by rw [at_.x6, o₁, ← BitVec.ofNat_add]; congr 1; simp only [src, k]; omega) (by omega)
    (by simp only [src, k]; omega)
  generalize h₁ : execInstrBr state (.LD .x5 .x6 (BitVec.ofNat 12 (8*m))) = s₁ at run₁ pc₁ mem₁ x5₁ keep₁
  have value : s₁.getReg .x5 = sourceWord sub input (114*k + 20*g + m) := by
    rw [x5₁, if_neg (by decide)]
    have e : state.getMem (BitVec.ofNat 64 (8*src)) = memoryView state src := rfl
    rw [e, at_.rest src (by simp only [src, k]; omega) (by right; left; simp only [src, k]; omega) (by right; omega)]
    unfold sourceWord
    rw [show src = proofWord + (114*k + 20*g + m) by simp only [src]; omega]
  -- store low copy
  obtain ⟨run₂, pc₂, view₂, keep₂⟩ := wrap_store wrap s₁ .x7 .x5 _ (10+4*m+1) c₂ pc₁ (TBW + 40*g + m)
    (by rw [keep₁ .x7 (by decide), at_.x7, o₁, ← BitVec.ofNat_add]; apply word_of_bytes; omega)
    (by omega)
  generalize h₂ : execInstrBr s₁ (.SD .x7 .x5 (BitVec.ofNat 12 (8*m))) = s₂ at run₂ pc₂ view₂ keep₂
  -- store high copy
  obtain ⟨run₃, pc₃, view₃, keep₃⟩ := wrap_store wrap s₂ .x7 .x5 _ (10+4*m+2) c₃ (by rw [pc₂]) (TBW + 40*g + 20 + m)
    (by rw [keep₂, keep₁ .x7 (by decide), at_.x7, o₂, ← BitVec.ofNat_add]; apply word_of_bytes; omega)
    (by omega)
  generalize h₃ : execInstrBr s₂ (.SD .x7 .x5 (BitVec.ofNat 12 (160+8*m))) = s₃ at run₃ pc₃ view₃ keep₃
  -- clear the source
  obtain ⟨run₄, pc₄, view₄, keep₄⟩ := wrap_store wrap s₃ .x6 .x0 _ (10+4*m+3) c₄ (by rw [pc₃]) src
    (by rw [keep₃, keep₂, keep₁ .x6 (by decide), at_.x6, o₁, ← BitVec.ofNat_add]; apply word_of_bytes;
        simp only [src, k]; omega)
    (by simp only [src, k]; omega)
  generalize h₄ : execInstrBr s₃ (.SD .x6 .x0 (BitVec.ofNat 12 (8*m))) = s₄ at run₄ pc₄ view₄ keep₄
  have regs (r : Reg) (a : r ≠ .x5) : s₄.getReg r = state.getReg r := by
    rw [keep₄, keep₃, keep₂, keep₁ r a]
  have stored : s₃.getReg .x5 = sourceWord sub input (114*k + 20*g + m) := by rw [keep₃, keep₂, value]
  have zero : s₃.getReg .x0 = 0 := rfl
  refine ⟨s₄, ((run₁.trans run₂).trans (run₃.trans run₄)).cast rfl rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [regs .x6 (by decide), at_.x6]
  · rw [regs .x7 (by decide), at_.x7]
  · rw [regs .x28 (by decide), at_.x28]
  · intro r member
    have : r ≠ .x5 := by intro h; subst h; simp [keptRegs] at member
    rw [regs r this, at_.kept r member]
  · intro x hx
    have hx' : TBW + x < 2^61 := by omega
    rw [view₄ _ hx', if_neg (by simp only [src, k]; omega), view₃ _ hx', view₂ _ hx']
    by_cases low : TBW + x = TBW + 40*g + m
    · rw [if_neg (by omega), if_pos low, value]
      unfold tableWord sourceWord
      rw [show x = 40*g + m by omega, show (40*g+m)/40 = g by omega, show (40*g+m)%40%20 = m by omega]
    · rw [if_neg low]
      by_cases high : TBW + x = TBW + 40*g + 20 + m
      · rw [if_pos high, keep₂, value]
        unfold tableWord sourceWord
        rw [show x = 40*g + 20 + m by omega, show (40*g+20+m)/40 = g by omega,
          show (40*g+20+m)%40%20 = m by omega]
      · rw [if_neg high, view_of_mem mem₁]
        exact at_.table x (by omega)
  · intro f hf
    have hf' : proofWord + 114*k + f < 2^61 := by omega
    rw [view₄ _ hf']
    by_cases here : proofWord + 114*k + f = src
    · rw [if_pos here, zero]
    · rw [if_neg here, view₃ _ hf', if_neg (by omega), view₂ _ hf', if_neg (by omega), view_of_mem mem₁]
      exact at_.cleared f (by simp only [src] at here; omega)
  · intro w hw t p
    rw [view₄ _ (by omega), if_neg (by simp only [src, k]; omega), view₃ _ (by omega), if_neg (by omega),
      view₂ _ (by omega), if_neg (by omega), view_of_mem mem₁]
    exact at_.rest w hw (by omega) (by omega)
  · rw [pc₄]
    congr 1


theorem group_start {sub : Submission} {input : CheckInput} {N g : Nat} {state : MachineState}
    (at_ : TableAt sub input N g state) : GroupAt sub input N g 0 state :=
  ⟨at_.x6, at_.x7, at_.x28, at_.kept, fun x hx => at_.table x (by omega), at_.cleared,
    fun w hw t p => at_.rest w hw (by omega) p⟩

theorem group_copies {sub : Submission} (lay : WrapLayout sub) (wrap : WrapImage (sub.image .check))
    (input : CheckInput) (N : Nat) (hN : N ≤ 55)
    (nonempty : input.positions.card ≠ 0) (g : Nat) (hg : g < N) :
    ∀ m ≤ 20, ∀ state : MachineState, state.pc = BitVec.ofNat 64 (4096+4*(460+10)) → GroupAt sub input N g 0 state →
      ∃ next : MachineState, Hop (sub.image .check) state next (4*m) (4*m) ∧ GroupAt sub input N g m next ∧
        next.pc = BitVec.ofNat 64 (4096+4*(460+(10+4*m))) := by
  intro m
  induction m with
  | zero => intro _ state pc at_; exact ⟨state, Hop.zero _ _, at_, by simpa using pc⟩
  | succ m ih =>
    intro le state pc at_
    obtain ⟨mid, run, atMid, pcMid⟩ := ih (by omega) state pc at_
    obtain ⟨next, run₂, atNext, pcNext⟩ := table_step lay wrap input N hN nonempty g m hg (by omega) mid pcMid atMid
    exact ⟨next, (run.trans run₂).cast (by omega) (by omega), atNext, pcNext⟩

theorem table_latch_code : WrapAt 90 [.ADDI .x6 .x6 160, .ADDI .x7 .x7 320, .ADDI .x28 .x28 4095] ∧
    wrapCode[93]? = some (.BNE .x28 .x0 7860) := by
  decide +kernel

/-- One whole group and the group latch. -/
theorem table_group {sub : Submission} (lay : WrapLayout sub) (wrap : WrapImage (sub.image .check))
    (input : CheckInput) (N : Nat) (hN : N ≤ 55)
    (nonempty : input.positions.card ≠ 0) (g : Nat) (hg : g < N) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (4096+4*(460+10))) (at_ : TableAt sub input N g state) :
    ∃ next : MachineState, Hop (sub.image .check) state next 84 84 ∧ TableAt sub input N (g+1) next ∧
      next.pc = BitVec.ofNat 64 (4096+4*(460+(if g+1 = N then 94 else 10))) := by
  have card : input.positions.card ≤ 16777216 := by
    have : input.positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ input.positions
    exact this
  have pb : PENTA_PROOF_BASE = 10804535392 := rfl
  have tb : TABLE = 268435456 := rfl
  obtain ⟨c₁, c₂⟩ := table_latch_code
  obtain ⟨s₁, run₁, at₁, pc₁⟩ := group_copies lay wrap input N hN nonempty g hg 20 le_rfl state pc (group_start at_)
  have pure₂ : ([.ADDI .x6 .x6 160, .ADDI .x7 .x7 320, .ADDI .x28 .x28 4095] : List Instr).all wrapPure = true := rfl
  have run₂ := wrap_pure_run wrap _ 90 s₁ c₁ pc₁ pure₂
  have pc₂ := wrap_pure_pc _ s₁ pure₂
  have mem₂ := wrap_pure_mem _ s₁ pure₂
  have x6₂ : (([.ADDI .x6 .x6 160, .ADDI .x7 .x7 320, .ADDI .x28 .x28 4095] : List Instr).foldl execInstrBr s₁).getReg .x6 =
      s₁.getReg .x6 + signExtend12 160 := by simp [execInstrBr, get_reg_set_reg]
  have x7₂ : (([.ADDI .x6 .x6 160, .ADDI .x7 .x7 320, .ADDI .x28 .x28 4095] : List Instr).foldl execInstrBr s₁).getReg .x7 =
      s₁.getReg .x7 + signExtend12 320 := by simp [execInstrBr, get_reg_set_reg]
  have x28₂ : (([.ADDI .x6 .x6 160, .ADDI .x7 .x7 320, .ADDI .x28 .x28 4095] : List Instr).foldl execInstrBr s₁).getReg .x28 =
      s₁.getReg .x28 + signExtend12 4095 := by simp [execInstrBr, get_reg_set_reg]
  have keep₂ (r : Reg) (a : r ≠ .x6) (b : r ≠ .x7) (c : r ≠ .x28) :
      (([.ADDI .x6 .x6 160, .ADDI .x7 .x7 320, .ADDI .x28 .x28 4095] : List Instr).foldl execInstrBr s₁).getReg r =
        s₁.getReg r := by
    simp [execInstrBr, get_reg_set_reg, Ne.symm a, Ne.symm b, Ne.symm c]
  generalize h₂ : ([.ADDI .x6 .x6 160, .ADDI .x7 .x7 320, .ADDI .x28 .x28 4095] : List Instr).foldl execInstrBr s₁ = s₂
    at run₂ pc₂ mem₂ x6₂ x7₂ x28₂ keep₂
  have count : s₂.getReg .x28 = BitVec.ofNat 64 (N - (g+1)) := by
    rw [x28₂, at₁.x28, show signExtend12 (4095 : BitVec 12) = BitVec.ofNat 64 (2^64-1) by decide, ← BitVec.ofNat_add]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    omega
  have run₃ := wrap_control wrap s₂ (.BNE .x28 .x0 7860) 93 c₂ (by rw [pc₂, pc₁, pc_add]; rfl) rfl rfl
  have shape : execInstrBr s₂ (.BNE .x28 .x0 7860) =
      s₂.setPC (if s₂.getReg .x28 != s₂.getReg .x0 then s₂.pc + signExtend13 7860 else s₂.pc + 4) := by
    simp only [execInstrBr]; split <;> rfl
  rw [shape] at run₃
  refine ⟨_, (run₁.trans (run₂.trans run₃)).cast (by simp) (by simp [wrapCost, instructionCycles]),
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [set_pc_reg, x6₂, at₁.x6, show signExtend12 (160 : BitVec 12) = BitVec.ofNat 64 160 by decide,
      ← BitVec.ofNat_add]
    congr 1
  · rw [set_pc_reg, x7₂, at₁.x7, show signExtend12 (320 : BitVec 12) = BitVec.ofNat 64 320 by decide,
      ← BitVec.ofNat_add]
    congr 1
  · rw [set_pc_reg, count]
  · intro r member
    have ne : r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x28 := by
      refine ⟨?_, ?_, ?_⟩ <;> (intro h; subst h; simp [keptRegs] at member)
    rw [set_pc_reg, keep₂ r ne.1 ne.2.1 ne.2.2, at₁.kept r member]
  · intro x hx
    rw [view_of_mem (set_pc_mem _ _), view_of_mem mem₂]
    exact at₁.table x (by omega)
  · intro f hf
    rw [view_of_mem (set_pc_mem _ _), view_of_mem mem₂]
    exact at₁.cleared f (by omega)
  · intro w hw t p
    rw [view_of_mem (set_pc_mem _ _), view_of_mem mem₂]
    exact at₁.rest w hw (by omega) (by omega)
  · rw [set_pc_pc, count, show s₂.getReg .x0 = 0#64 from rfl, pc₂, pc₁, pc_add]
    by_cases last : g+1 = N
    · rw [if_pos last, show N - (g+1) = 0 by omega]
      decide
    · rw [if_neg last]
      have nonzero : BitVec.ofNat 64 (N - (g+1)) ≠ 0#64 := by
        intro same
        have := congrArg BitVec.toNat same
        simp only [BitVec.toNat_ofNat] at this
        omega
      simp only [bne_iff_ne, ne_eq, nonzero, not_false_eq_true, if_true]
      decide

/-- The whole table phase. -/
theorem table_loop {sub : Submission} (lay : WrapLayout sub) (wrap : WrapImage (sub.image .check))
    (input : CheckInput) (N : Nat) (hN : N ≤ 55) (positive : 0 < N)
    (nonempty : input.positions.card ≠ 0) :
    ∀ g ≤ N, ∀ state : MachineState, state.pc = BitVec.ofNat 64 (4096+4*(460+10)) →
      TableAt sub input N 0 state →
      ∃ next : MachineState, Hop (sub.image .check) state next (84*g) (84*g) ∧ TableAt sub input N g next ∧
        next.pc = BitVec.ofNat 64 (4096+4*(460+(if g = N then 94 else 10))) := by
  intro g
  induction g with
  | zero => intro _ state pc at_; exact ⟨state, Hop.zero _ _, at_, by rw [if_neg (by omega)]; exact pc⟩
  | succ g ih =>
    intro le state pc at_
    obtain ⟨mid, run, atMid, pcMid⟩ := ih (by omega) state pc at_
    have pcLoop : mid.pc = BitVec.ofNat 64 (4096+4*(460+10)) := by
      rw [pcMid, if_neg (by omega)]
    obtain ⟨next, run₂, atNext, pcNext⟩ := table_group lay wrap input N hN nonempty g (by omega) mid pcLoop atMid
    exact ⟨next, (run.trans run₂).cast (by ring) (by ring), atNext, pcNext⟩

end TwoPermutationPrototype.PentaWrap
