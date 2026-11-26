import CommitGolfCandidate.PentaWrapRecord

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

/-- The donor checker's state after its word 0 on the expanded input, outside the scratch table. -/
structure WrapExit (sub : Submission) (input : CheckInput) (state : MachineState) : Prop where
  pc : state.pc = BitVec.ofNat 64 4100
  factor : state.getReg .x6 = BitVec.ofNat 64 1424
  regs : ∀ r, r ≠ .x6 → state.getReg r = (sub.initialState .check (expandInput input)).getReg r
  memory : ∀ w < 2^33, (w < TBW ∨ TBW + 2200 ≤ w) →
    memoryView state w = memoryView (sub.initialState .check (expandInput input)) w

theorem run_codes :
    wrapCode[0]? = some (.BEQ .x16 .x0 1236) ∧
    WrapAt 1 [.ADDI .x30 .x0 912, .MUL .x30 .x16 .x30, .LUI .x31 2, .ADDI .x31 .x31 512, .ADD .x31 .x30 .x31] ∧
    wrapCode[6]? = some (.BNE .x17 .x31 1224) ∧
    WrapAt 7 [.ADD .x6 .x15 .x30, .LUI .x7 65536, .ADDI .x28 .x0 55] ∧
    WrapAt 94 constantCode ∧ WrapAt 106 pointerCode ∧
    WrapAt 288 ([.ADDI .x6 .x0 1424, .MUL .x17 .x16 .x6] ++ zeroedRegs.map (fun r => .ADDI r .x0 0)) ∧
    wrapCode[308]? = some (.JAL .x0 2094084) ∧
    wrapCode[309]? = some (.BNE .x17 .x0 12) ∧ WrapAt 310 [.ADDI .x6 .x0 1424] ∧
    wrapCode[311]? = some (.JAL .x0 2094072) ∧
    WrapAt 312 [.ADDI .x5 .x0 1, .ADDI .x10 .x0 1] ∧ wrapCode[314]? = some .ECALL := by
  decide +kernel

theorem card_bound' (positions : Positions) : positions.card ≤ 16777216 := by
  have : positions.card ≤ LENGTH := by simpa [Index] using Finset.card_le_univ positions
  exact this

/-! ### Entry, reject and empty paths -/

theorem entry_hop {sub : Submission} (wrap : WrapImage (sub.image .check)) (input : CheckInput) :
    Hop (sub.image .check) (sub.initialState .check input)
      ((sub.initialState .check input).setPC (BitVec.ofNat 64 (4096+4*(460+0)))) 1 1 := by
  have e : execInstrBr (sub.initialState .check input) (.JAL .x0 1840) =
      (sub.initialState .check input).setPC (BitVec.ofNat 64 (4096+4*(460+0))) := by
    simp only [execInstrBr]
    rw [loader_pc]
    rfl
  have stepped : ordinaryStep (sub.initialState .check input) (.base (.JAL .x0 1840)) =
      some ((sub.initialState .check input).setPC (BitVec.ofNat 64 (4096+4*(460+0)))) := by
    rw [← e]; rfl
  intro fuel
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ (entry_fetch wrap _ (loader_pc sub input)) stepped]
  rfl

/-- Words 772-774 (offsets 312-314): HALT with exit code 1. -/
theorem reject_run {sub : Submission} (wrap : WrapImage (sub.image .check)) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (4096+4*(460+312))) :
    ∃ final : MachineState, ∀ fuel, execute (sub.image .check) (3+fuel) state false =
      pure ⟨.failure, final, 3, 0⟩ := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, c₁, c₂⟩ := run_codes
  have pure₁ : ([.ADDI .x5 .x0 1, .ADDI .x10 .x0 1] : List Instr).all wrapPure = true := rfl
  have run₁ := wrap_pure_run wrap _ 312 state c₁ pc pure₁
  have pc₁ := wrap_pure_pc _ state pure₁
  have x5 : (([.ADDI .x5 .x0 1, .ADDI .x10 .x0 1] : List Instr).foldl execInstrBr state).getReg .x5 = 1 := by
    have z : state.getReg .x0 = 0#64 := rfl
    simp [execInstrBr, get_reg_set_reg, z]
    decide
  have x10 : (([.ADDI .x5 .x0 1, .ADDI .x10 .x0 1] : List Instr).foldl execInstrBr state).getReg .x10 = 1 := by
    have z : state.getReg .x0 = 0#64 := rfl
    simp [execInstrBr, get_reg_set_reg, z]
    decide
  generalize h₁ : ([.ADDI .x5 .x0 1, .ADDI .x10 .x0 1] : List Instr).foldl execInstrBr state = s₁ at run₁ pc₁ x5 x10
  have halted := wrap_fetch wrap s₁ 314 .ECALL c₂ (by rw [pc₁, pc, pc_add]; rfl)
  have run₁' := run₁.cast (show [Instr.ADDI .x5 .x0 1, .ADDI .x10 .x0 1].length = 2 from rfl)
    (show wrapCost [Instr.ADDI .x5 .x0 1, .ADDI .x10 .x0 1] = 2 by simp [wrapCost, instructionCycles])
  refine ⟨s₁, fun fuel => ?_⟩
  rw [show 3+fuel = 2+(fuel+1) by omega, run₁' (fuel+1)]
  simp [execute, halted, x5, x10, Execution.charge, wrapCost, instructionCycles]

theorem bne_shape (state : MachineState) (r₁ r₂ : Reg) (imm : BitVec 13) :
    execInstrBr state (.BNE r₁ r₂ imm) =
      state.setPC (if state.getReg r₁ != state.getReg r₂ then state.pc + signExtend13 imm else state.pc + 4) := by
  simp only [execInstrBr]; split <;> rfl

theorem beq_shape (state : MachineState) (r₁ r₂ : Reg) (imm : BitVec 13) :
    execInstrBr state (.BEQ r₁ r₂ imm) =
      state.setPC (if state.getReg r₁ == state.getReg r₂ then state.pc + signExtend13 imm else state.pc + 4) := by
  simp only [execInstrBr]; split <;> rfl

theorem word_ne_zero (n : Nat) (hn : n ≠ 0) (small : n < 2^64) : BitVec.ofNat 64 n ≠ 0#64 := by
  intro same
  have := congrArg BitVec.toNat same
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small] at this
  exact hn (by simpa using this)

theorem word_eq_iff (a b : Nat) (ha : a < 2^64) (hb : b < 2^64) : BitVec.ofNat 64 a = BitVec.ofNat 64 b ↔ a = b := by
  constructor
  · intro same
    have := congrArg BitVec.toNat same
    simp only [BitVec.toNat_ofNat] at this
    omega
  · intro h; rw [h]


/-! ### Guard -/

def guardMid : List Instr := [.ADDI .x30 .x0 912, .MUL .x30 .x16 .x30, .LUI .x31 2, .ADDI .x31 .x31 512, .ADD .x31 .x30 .x31]
def guardTail : List Instr := [.ADD .x6 .x15 .x30, .LUI .x7 65536, .ADDI .x28 .x0 55]

theorem guard_mid_regs (state : MachineState) (k : Nat) (hk : k ≤ 16777216)
    (x16 : state.getReg .x16 = BitVec.ofNat 64 k) :
    (guardMid.foldl execInstrBr state).getReg .x30 = BitVec.ofNat 64 (912*k) ∧
    (guardMid.foldl execInstrBr state).getReg .x31 = BitVec.ofNat 64 (912*k + 8704) ∧
    ∀ r, r ≠ .x30 → r ≠ .x31 → (guardMid.foldl execInstrBr state).getReg r = state.getReg r := by
  have z : state.getReg .x0 = 0#64 := rfl
  refine ⟨?_, ?_, ?_⟩
  · simp [guardMid, execInstrBr, get_reg_set_reg, z, x16]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_mul, signExtend12]
    omega
  · simp [guardMid, execInstrBr, get_reg_set_reg, z, x16]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_mul, BitVec.toNat_add, signExtend12]
    omega
  · intro r a b
    simp [guardMid, execInstrBr, get_reg_set_reg, Ne.symm a, Ne.symm b]

theorem guard_tail_regs (state : MachineState) (k : Nat) (hk : k ≤ 16777216)
    (x15 : state.getReg .x15 = BitVec.ofNat 64 10804535392) (x30 : state.getReg .x30 = BitVec.ofNat 64 (912*k)) :
    (guardTail.foldl execInstrBr state).getReg .x6 = BitVec.ofNat 64 (PENTA_PROOF_BASE + 912*k + 160*0) ∧
    (guardTail.foldl execInstrBr state).getReg .x7 = BitVec.ofNat 64 (TABLE + 320*0) ∧
    (guardTail.foldl execInstrBr state).getReg .x28 = BitVec.ofNat 64 (55 - 0) ∧
    ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x28 → (guardTail.foldl execInstrBr state).getReg r = state.getReg r := by
  have z : state.getReg .x0 = 0#64 := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [guardTail, execInstrBr, get_reg_set_reg, x15, x30, PENTA_PROOF_BASE, ← BitVec.ofNat_add]
  · simp [guardTail, execInstrBr, get_reg_set_reg, TABLE] <;> decide
  · simp [guardTail, execInstrBr, get_reg_set_reg, z] <;> decide
  · intro r a b c
    simp [guardTail, execInstrBr, get_reg_set_reg, Ne.symm a, Ne.symm b, Ne.symm c]

theorem kept_ne (r : Reg) (member : r ∈ keptRegs) :
    r ≠ .x5 ∧ r ≠ .x6 ∧ r ≠ .x7 ∧ r ≠ .x28 ∧ r ≠ .x30 ∧ r ≠ .x31 := by
  simp [keptRegs] at member
  rcases member with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide

/-- Non-empty openings: the length test, then the table phase's start. -/
theorem guard_run {sub : Submission} (lay : WrapLayout sub) (wrap : WrapImage (sub.image .check))
    (input : CheckInput) (nonempty : input.positions.card ≠ 0) (admitted : input.proof.length ≤ 23890755584) :
    ∃ state : MachineState,
      Hop (sub.image .check) ((sub.initialState .check input).setPC (BitVec.ofNat 64 (4096+4*(460+0)))) state 7 10 ∧
      state.getReg .x30 = BitVec.ofNat 64 (912*input.positions.card) ∧
      state.mem = (sub.initialState .check input).mem ∧
      (∀ r, r ≠ .x30 → r ≠ .x31 → state.getReg r = (sub.initialState .check input).getReg r) ∧
      state.pc = BitVec.ofNat 64 (4096+4*(460+(if input.proof.length = capLength input.positions then 7 else 312))) := by
  obtain ⟨c₀, c₁, c₂, _⟩ := run_codes
  have card := card_bound' input.positions
  let init := sub.initialState .check input
  let s₀ := init.setPC (BitVec.ofNat 64 (4096+4*(460+0)))
  have reg₀ (r : Reg) : s₀.getReg r = init.getReg r := rfl
  have x16 : s₀.getReg .x16 = BitVec.ofNat 64 input.positions.card := by rw [reg₀, loader_reg lay]; rfl
  have x17 : s₀.getReg .x17 = BitVec.ofNat 64 input.proof.length := by rw [reg₀, loader_reg lay]; rfl
  -- empty test (not taken)
  have run₁ := wrap_control wrap s₀ (.BEQ .x16 .x0 1236) 0 c₀ rfl rfl rfl
  rw [beq_shape] at run₁
  have notZero : (s₀.getReg .x16 == s₀.getReg .x0) = false := by
    rw [x16, show s₀.getReg .x0 = 0#64 from rfl]
    simpa using word_ne_zero _ nonempty (by omega)
  rw [notZero] at run₁
  simp only [Bool.false_eq_true, if_false] at run₁
  generalize h₁ : s₀.setPC (s₀.pc + 4) = s₁ at run₁
  have reg₁ (r : Reg) : s₁.getReg r = init.getReg r := by rw [← h₁, set_pc_reg]; rfl
  have pc₁ : s₁.pc = BitVec.ofNat 64 (4096+4*(460+1)) := by rw [← h₁, set_pc_pc]; rfl
  have mem₁ : s₁.mem = init.mem := by rw [← h₁, set_pc_mem]; rfl
  -- expected length
  have pure₂ : guardMid.all wrapPure = true := rfl
  have run₂ := wrap_pure_run wrap guardMid 1 s₁ c₁ pc₁ pure₂
  have pc₂ := wrap_pure_pc guardMid s₁ pure₂
  have mem₂ := wrap_pure_mem guardMid s₁ pure₂
  obtain ⟨x30₂, x31₂, keep₂⟩ := guard_mid_regs s₁ _ card (by rw [reg₁]; exact x16)
  generalize h₂ : guardMid.foldl execInstrBr s₁ = s₂ at run₂ pc₂ mem₂ x30₂ x31₂ keep₂
  -- length test
  have run₃ := wrap_control wrap s₂ (.BNE .x17 .x31 1224) 6 c₂ (by rw [pc₂, pc₁, pc_add]; rfl) rfl rfl
  rw [bne_shape] at run₃
  refine ⟨_, (run₁.trans (run₂.trans run₃)).cast rfl (by simp [guardMid, wrapCost, instructionCycles]),
    ?_, ?_, ?_, ?_⟩
  · rw [set_pc_reg, x30₂]
  · rw [set_pc_mem, mem₂, mem₁]
  · intro r a b
    rw [set_pc_reg, keep₂ r a b, reg₁]
  · rw [set_pc_pc, keep₂ .x17 (by decide) (by decide), reg₁, show init.getReg .x17 = s₀.getReg .x17 from rfl, x17,
      x31₂, pc₂, pc₁]
    by_cases same : input.proof.length = capLength input.positions
    · have eq : input.proof.length = 912*input.positions.card + 8704 := by
        rw [same]; unfold capLength; simp [nonempty]
      rw [if_pos same, eq]
      simp only [bne_self_eq_false, Bool.false_eq_true, if_false]
      rw [pc_add]
      rfl
    · have ne : BitVec.ofNat 64 input.proof.length ≠ BitVec.ofNat 64 (912*input.positions.card + 8704) := by
        intro h
        have := (word_eq_iff _ _ (by omega) (by omega)).mp h
        apply same
        rw [this]; unfold capLength; simp [nonempty]
      rw [if_neg same]
      simp only [bne_iff_ne, ne_eq, ne, not_false_eq_true, if_true]
      rw [pc_add]
      decide


end TwoPermutationPrototype.PentaWrap
