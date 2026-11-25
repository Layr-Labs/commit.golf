import CommitGolfCandidate.PentaWrapRunA

/-! The whole checker wrapper: from the loader state of a check input either
* the exact-length test fails and the wrapper halts with failure after at most 11 steps and no
  oracle call, or
* it reaches donor word 1 in a state that agrees with the donor checker's state after its word 0
  on the expanded input (`expandInput`): the same registers (`t1 = 1424`, `a7 = 1424k`) and the same
  aligned memory everywhere outside the doubled table in scratch memory (`WrapExit`).

The empty opening (k = 0) needs an empty proof; the wrapper then changes nothing but `t1`. -/

namespace TwoPermutationPrototype.PentaWrap
open CommitGolf CommitGolf.Riscv CommitGolfCandidate RiscvZkvm.Rv64 OracleComp TwoPermutationPrototype.Sampling
open TwoPermutationPrototype.RV64 (memoryView wordAddress)

set_option maxRecDepth 100000

/-! ### From the length test to the record loop -/

theorem beyond_zero {sub : Submission} (lay : WrapLayout sub) (input : CheckInput) (u : Nat)
    (past : input.proof.length ≤ 8*u) (small : proofWord + u < 2^33) :
    memoryView (sub.initialState .check input) (proofWord + u) = 0 := by
  rw [proof_word lay input u small]
  have none (j : Nat) : input.proof[8*u+j]? = none := List.getElem?_eq_none (by omega)
  simp [none]

theorem table_start {sub : Submission} (lay : WrapLayout sub) (wrap : WrapImage (sub.image .check))
    (input : CheckInput) (state : MachineState) (pc : state.pc = BitVec.ofNat 64 (4096+4*(460+7)))
    (x30 : state.getReg .x30 = BitVec.ofNat 64 (912*input.positions.card))
    (mem : state.mem = (sub.initialState .check input).mem)
    (regs : ∀ r, r ≠ .x30 → r ≠ .x31 → state.getReg r = (sub.initialState .check input).getReg r) :
    ∃ next : MachineState, Hop (sub.image .check) state next 3 3 ∧ TableAt sub input 0 next ∧
      next.pc = BitVec.ofNat 64 (4096+4*(460+10)) := by
  obtain ⟨_, _, _, c₃, _⟩ := run_codes
  have card := card_bound' input.positions
  have pure₁ : guardTail.all wrapPure = true := rfl
  have run₁ := wrap_pure_run wrap guardTail 7 state c₃ pc pure₁
  have pc₁ := wrap_pure_pc guardTail state pure₁
  have mem₁ := wrap_pure_mem guardTail state pure₁
  obtain ⟨x6₁, x7₁, x28₁, keep₁⟩ := guard_tail_regs state _ card
    (by rw [regs .x15 (by decide) (by decide), loader_reg lay]; rfl) x30
  generalize h₁ : guardTail.foldl execInstrBr state = s₁ at run₁ pc₁ mem₁ x6₁ x7₁ x28₁ keep₁
  refine ⟨s₁, run₁.cast rfl (by simp [guardTail, wrapCost, instructionCycles]), ⟨x6₁, x7₁, x28₁, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro r member
    obtain ⟨_, a, b, c, d, e⟩ := kept_ne r member
    rw [keep₁ r a b c, regs r d e]
  · intro x hx; omega
  · intro f hf; omega
  · intro w hw _ _
    rw [view_of_mem mem₁, view_of_mem mem]
  · rw [pc₁, pc, pc_add]; rfl

theorem constant_regs (state : MachineState) :
    Consts (constantCode.foldl execInstrBr state) ∧
    ∀ r ∉ constRegs, (constantCode.foldl execInstrBr state).getReg r = state.getReg r := by
  have z : state.getReg .x0 = 0#64 := rfl
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ <;>
    try (simp [constantCode, execInstrBr, get_reg_set_reg, z, TABLE, capFirst] <;> decide)
  intro r out
  simp [constRegs] at out
  simp [constantCode, execInstrBr, get_reg_set_reg, Ne.symm out.1, Ne.symm out.2.1, Ne.symm out.2.2.1,
    Ne.symm out.2.2.2.1, Ne.symm out.2.2.2.2.1, Ne.symm out.2.2.2.2.2.1, Ne.symm out.2.2.2.2.2.2]

theorem pointer_regs (state : MachineState) (k : Nat) (hk : 1 ≤ k) (hk' : k ≤ 16777216)
    (x16 : state.getReg .x16 = BitVec.ofNat 64 k) (x15 : state.getReg .x15 = BitVec.ofNat 64 10804535392)
    (x13 : state.getReg .x13 = BitVec.ofNat 64 6375350304) :
    (pointerCode.foldl execInstrBr state).getReg .x24 = BitVec.ofNat 64 (PENTA_PROOF_BASE + 912*k - 912) ∧
    (pointerCode.foldl execInstrBr state).getReg .x25 = BitVec.ofNat 64 (PENTA_PROOF_BASE + 1424*k - 1424) ∧
    (pointerCode.foldl execInstrBr state).getReg .x26 = BitVec.ofNat 64 (6375350304 + 8*k - 8) ∧
    ∀ r, r ≠ .x24 → r ≠ .x25 → r ≠ .x26 → r ≠ .x30 → r ≠ .x31 →
      (pointerCode.foldl execInstrBr state).getReg r = state.getReg r := by
  have z : state.getReg .x0 = 0#64 := rfl
  have pb : PENTA_PROOF_BASE = 10804535392 := rfl
  have pred : state.getReg .x16 + signExtend12 4095 = BitVec.ofNat 64 (k-1) := by
    rw [x16]; exact neg_imm k 1 4095 hk (by omega) (by decide)
  have c912 : state.getReg .x0 + signExtend12 912 = BitVec.ofNat 64 912 := by rw [z]; decide
  have c1424 : state.getReg .x0 + signExtend12 1424 = BitVec.ofNat 64 1424 := by rw [z]; decide
  have e24 : (pointerCode.foldl execInstrBr state).getReg .x24 =
      state.getReg .x15 + (state.getReg .x16 + signExtend12 4095) * (state.getReg .x0 + signExtend12 912) := rfl
  have e25 : (pointerCode.foldl execInstrBr state).getReg .x25 =
      state.getReg .x15 + (state.getReg .x16 + signExtend12 4095) * (state.getReg .x0 + signExtend12 1424) := rfl
  have e26 : (pointerCode.foldl execInstrBr state).getReg .x26 =
      state.getReg .x13 + (state.getReg .x16 + signExtend12 4095) <<< (3 : BitVec 6).toNat := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e24, pred, c912, x15, ← BitVec.ofNat_mul, ← BitVec.ofNat_add]
    congr 1
    rw [pb]; omega
  · rw [e25, pred, c1424, x15, ← BitVec.ofNat_mul, ← BitVec.ofNat_add]
    congr 1
    rw [pb]; omega
  · rw [e26, pred, x13]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_shiftLeft]
    simp only [BitVec.toNat_ofNat, Nat.shiftLeft_eq, show (3 : BitVec 6).toNat = 3 from rfl]
    omega
  · intro r a b c d e
    simp [pointerCode, execInstrBr, get_reg_set_reg, Ne.symm a, Ne.symm b, Ne.symm c, Ne.symm d, Ne.symm e]

/-- Constants and pointers: the record loop's start. -/
theorem loop_start {sub : Submission} (lay : WrapLayout sub) (wrap : WrapImage (sub.image .check))
    (input : CheckInput) (nonempty : input.positions.card ≠ 0)
    (exact : input.proof.length = capLength input.positions)
    (state : MachineState) (pc : state.pc = BitVec.ofNat 64 (4096+4*(460+94)))
    (at_ : TableAt sub input 55 state) :
    ∃ next : MachineState, Hop (sub.image .check) state next 21 27 ∧ Expanding sub input input.positions.card next ∧
      next.pc = BitVec.ofNat 64 (4096+4*(460+115)) := by
  obtain ⟨_, _, _, _, c₄, c₅, _⟩ := run_codes
  have card := card_bound' input.positions
  have pw : proofWord = 1350566924 := rfl
  have tw : TBW = 33554432 := rfl
  have pure₁ : constantCode.all wrapPure = true := rfl
  have run₁ := wrap_pure_run wrap constantCode 94 state c₄ pc pure₁
  have pc₁ := wrap_pure_pc constantCode state pure₁
  have mem₁ := wrap_pure_mem constantCode state pure₁
  obtain ⟨consts₁, keep₁⟩ := constant_regs state
  generalize h₁ : constantCode.foldl execInstrBr state = s₁ at run₁ pc₁ mem₁ consts₁ keep₁
  have keptOut : ∀ r ∈ keptRegs, r ∉ constRegs := by decide
  have kept₁ (r : Reg) (member : r ∈ keptRegs) : s₁.getReg r = (sub.initialState .check input).getReg r :=
    (keep₁ r (keptOut r member)).trans (at_.kept r member)
  have pure₂ : pointerCode.all wrapPure = true := rfl
  have run₂ := wrap_pure_run wrap pointerCode 106 s₁ c₅ (by rw [pc₁, pc, pc_add]; rfl) pure₂
  have pc₂ := wrap_pure_pc pointerCode s₁ pure₂
  have mem₂ := wrap_pure_mem pointerCode s₁ pure₂
  obtain ⟨x24₂, x25₂, x26₂, keep₂⟩ := pointer_regs s₁ _ (by omega) card
    (by rw [kept₁ .x16 (by decide), loader_reg lay]; rfl) (by rw [kept₁ .x15 (by decide), loader_reg lay]; rfl)
    (by rw [kept₁ .x13 (by decide), loader_reg lay]; rfl)
  generalize h₂ : pointerCode.foldl execInstrBr s₁ = s₂ at run₂ pc₂ mem₂ x24₂ x25₂ x26₂ keep₂
  have pointOut : ∀ r ∈ keptRegs ++ constRegs, r ≠ .x24 ∧ r ≠ .x25 ∧ r ≠ .x26 ∧ r ≠ .x30 ∧ r ≠ .x31 := by decide
  refine ⟨s₂, (run₁.trans run₂).cast rfl (by simp [constantCode, pointerCode, wrapCost, instructionCycles]),
    ⟨x24₂, x25₂, x26₂, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact consts₁.keep (fun r member => by
      obtain ⟨a, b, c, d, e⟩ := pointOut r (List.mem_append_right _ member); exact keep₂ r a b c d e)
  · intro r member
    obtain ⟨a, b, c, d, e⟩ := pointOut r (List.mem_append_left _ member)
    rw [keep₂ r a b c d e, kept₁ r member]
  · intro x hx
    rw [view_of_mem mem₂, view_of_mem mem₁]
    exact at_.table x (by omega)
  · intro w hw side
    rw [view_of_mem mem₂, view_of_mem mem₁]
    exact at_.rest w (by omega) (by omega) (by left; exact hw)
  · intro w lo hi; omega
  · intro w hw lo
    rw [view_of_mem mem₂, view_of_mem mem₁]
    by_cases cleared : w < proofWord + 114*input.positions.card + 1100
    · have := at_.cleared (w - (proofWord + 114*input.positions.card)) (by omega)
      rwa [show proofWord + 114*input.positions.card + (w - (proofWord + 114*input.positions.card)) = w by omega]
        at this
    · rw [at_.rest w hw (by omega) (by omega)]
      obtain ⟨u, rfl⟩ : ∃ u, w = proofWord + u := ⟨w - proofWord, by omega⟩
      apply beyond_zero lay input u (by rw [exact]; unfold capLength; simp [nonempty]; omega) hw
  · rw [pc₂, pc₁, pc, pc_add, pc_add]; rfl


end TwoPermutationPrototype.PentaWrap
