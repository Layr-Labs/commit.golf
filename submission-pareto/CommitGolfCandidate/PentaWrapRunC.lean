import CommitGolfCandidate.PentaWrapRunB

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

/-! ### Restore and the empty case -/

def restoreBody : List Instr := [.ADDI .x6 .x0 1424, .MUL .x17 .x16 .x6] ++ zeroedRegs.map (fun r => .ADDI r .x0 0)

theorem restore_x6 (state : MachineState) :
    (restoreBody.foldl execInstrBr state).getReg .x6 = BitVec.ofNat 64 1424 := by
  have z : state.getReg .x0 = 0#64 := rfl
  simp [restoreBody, zeroedRegs, execInstrBr, get_reg_set_reg, z]
  decide

theorem restore_x17 (state : MachineState) (k : Nat) (hk : k ≤ 16777216)
    (x16 : state.getReg .x16 = BitVec.ofNat 64 k) :
    (restoreBody.foldl execInstrBr state).getReg .x17 = BitVec.ofNat 64 (1424*k) := by
  have z : state.getReg .x0 = 0#64 := rfl
  simp [restoreBody, zeroedRegs, execInstrBr, get_reg_set_reg, z, x16]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, signExtend12]
  omega

theorem restore_zero (state : MachineState) (r : Reg) (member : r ∈ zeroedRegs) :
    (restoreBody.foldl execInstrBr state).getReg r = 0 := by
  have z : state.getReg .x0 = 0#64 := rfl
  simp only [zeroedRegs, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
    simp [restoreBody, zeroedRegs, execInstrBr, get_reg_set_reg, z] <;> decide

theorem restore_keep (state : MachineState) (r : Reg) (a : r ≠ .x6) (b : r ≠ .x17) (c : r ∉ zeroedRegs) :
    (restoreBody.foldl execInstrBr state).getReg r = state.getReg r := by
  simp only [zeroedRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at c
  simp [restoreBody, zeroedRegs, execInstrBr, get_reg_set_reg, Ne.symm a, Ne.symm b, Ne.symm c.1, Ne.symm c.2.1,
    Ne.symm c.2.2.1, Ne.symm c.2.2.2.1, Ne.symm c.2.2.2.2.1, Ne.symm c.2.2.2.2.2.1, Ne.symm c.2.2.2.2.2.2.1,
    Ne.symm c.2.2.2.2.2.2.2.1, Ne.symm c.2.2.2.2.2.2.2.2.1, Ne.symm c.2.2.2.2.2.2.2.2.2.1,
    Ne.symm c.2.2.2.2.2.2.2.2.2.2.1, Ne.symm c.2.2.2.2.2.2.2.2.2.2.2.1, Ne.symm c.2.2.2.2.2.2.2.2.2.2.2.2.1,
    Ne.symm c.2.2.2.2.2.2.2.2.2.2.2.2.2.1, Ne.symm c.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    Ne.symm c.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, Ne.symm c.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    Ne.symm c.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2]

/-- Registers the loader sets to zero are exactly the zeroed ones and `x0`, `x1`, `x3`, `x4`, `x6`. -/
theorem loader_zeroed (k L : Nat) (r : Reg) (member : r ∈ zeroedRegs) : loaderReg k L r = 0 := by
  simp only [zeroedRegs, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> rfl

theorem loader_length_free (k L L' : Nat) (r : Reg) (h : r ≠ .x17) : loaderReg k L r = loaderReg k L' r := by
  cases r <;> first | rfl | exact absurd rfl h

theorem reg_classes (r : Reg) : r = .x0 ∨ r = .x6 ∨ r = .x17 ∨ r ∈ zeroedRegs ∨ r ∈ keptRegs := by
  cases r <;> simp [zeroedRegs, keptRegs]

/-- The register file at donor word 1 from the loaded registers. -/
theorem exit_regs {sub : Submission} (lay : WrapLayout sub) (input : CheckInput) (state : MachineState)
    (x17 : state.getReg .x17 = BitVec.ofNat 64 (1424*input.positions.card))
    (zeroed : ∀ r ∈ zeroedRegs, state.getReg r = 0)
    (kept : ∀ r ∈ keptRegs, r ≠ .x17 → state.getReg r = (sub.initialState .check input).getReg r) :
    ∀ r, r ≠ .x6 → state.getReg r = (sub.initialState .check (expandInput input)).getReg r := by
  intro r ne
  rw [loader_reg lay]
  have length : (expandInput input).proof.length = 1424*input.positions.card := expand_proof_length _ _
  rcases reg_classes r with h | h | h | h | h
  · subst h; rfl
  · exact absurd h ne
  · subst h; rw [x17, length]; rfl
  · rw [zeroed r h, loader_zeroed _ _ r h]
  · by_cases h17 : r = .x17
    · subst h17; rw [x17, length]; rfl
    · rw [kept r h h17, loader_reg lay, length]
      exact loader_length_free _ _ _ r h17


theorem exit_pc (state : MachineState) (pc : state.pc = BitVec.ofNat 64 (4096+4*(460+308))) :
    (execInstrBr state (.JAL .x0 2094084)).pc = BitVec.ofNat 64 4100 := by
  simp only [execInstrBr]
  show state.pc + signExtend21 2094084 = _
  rw [pc]; decide

theorem jal_keeps (state : MachineState) (imm : BitVec 21) :
    (execInstrBr state (.JAL .x0 imm)).mem = state.mem ∧ ∀ r, (execInstrBr state (.JAL .x0 imm)).getReg r = state.getReg r := by
  refine ⟨rfl, fun r => rfl⟩

/-- The restore (offsets 288-308): every temporary zeroed, `a7 = 1424k`, `t1 = 1424`, jump to word 1. -/
theorem restore_run {sub : Submission} (lay : WrapLayout sub) (wrap : WrapImage (sub.image .check))
    (input : CheckInput) (exact : input.proof.length = capLength input.positions)
    (state : MachineState) (pc : state.pc = BitVec.ofNat 64 (4096+4*(460+288)))
    (at_ : Expanding sub input 0 state) :
    ∃ final : MachineState, Hop (sub.image .check) state final 21 24 ∧ WrapExit sub input final := by
  obtain ⟨_, _, _, _, _, _, c₆, c₇, _⟩ := run_codes
  have card := card_bound' input.positions
  have pw : proofWord = 1350566924 := rfl
  have tw : TBW = 33554432 := rfl
  have pure₁ : restoreBody.all wrapPure = true := by unfold restoreBody; simp [zeroedRegs, wrapPure]
  have run₁ := wrap_pure_run wrap restoreBody 288 state c₆ pc pure₁
  have pc₁ := wrap_pure_pc restoreBody state pure₁
  have mem₁ := wrap_pure_mem restoreBody state pure₁
  have x6₁ := restore_x6 state
  have x17₁ := restore_x17 state input.positions.card card
    (by rw [at_.kept .x16 (by decide), loader_reg lay]; rfl)
  have zero₁ := restore_zero state
  have keep₁ := restore_keep state
  generalize h₁ : restoreBody.foldl execInstrBr state = s₁ at run₁ pc₁ mem₁ x6₁ x17₁ zero₁ keep₁
  have run₂ := wrap_control wrap s₁ (.JAL .x0 2094084) 308 c₇ (by rw [pc₁, pc, pc_add]; rfl) rfl rfl
  obtain ⟨mem₂, reg₂⟩ := jal_keeps s₁ 2094084
  have pc₂ := exit_pc s₁ (by rw [pc₁, pc, pc_add]; rfl)
  generalize h₂ : execInstrBr s₁ (.JAL .x0 2094084) = s₂ at run₂ mem₂ reg₂ pc₂
  refine ⟨s₂, (run₁.trans run₂).cast (by unfold restoreBody; simp [zeroedRegs])
      (by unfold restoreBody; simp [zeroedRegs, wrapCost, instructionCycles]), pc₂, by rw [reg₂, x6₁], ?_, ?_⟩
  · apply exit_regs lay input s₂ (by rw [reg₂, x17₁]) (fun r hr => by rw [reg₂, zero₁ r hr])
    intro r member h17
    have h6 : r ≠ .x6 := by intro e; subst e; simp [keptRegs] at member
    have disjoint : ∀ r ∈ keptRegs, r ∉ zeroedRegs := by decide
    have hz : r ∉ zeroedRegs := disjoint r member
    rw [reg₂, keep₁ r h6 h17 hz, at_.kept r member]
  · intro w hw side
    rw [expanded_loader lay input exact w hw, view_of_mem mem₂, view_of_mem mem₁]
    unfold expandedTarget
    by_cases low : w < proofWord
    · rw [if_pos low]; exact at_.low w (by omega) side
    · rw [if_neg low]
      by_cases area : w < proofWord + 178*input.positions.card
      · rw [if_pos area]; exact at_.done w (by omega) area
      · rw [if_neg area]; exact at_.high w hw (by omega)

/-- The empty opening with the empty proof: only `t1` changes. -/
theorem empty_run {sub : Submission} (lay : WrapLayout sub) (wrap : WrapImage (sub.image .check))
    (input : CheckInput) (empty : input.positions.card = 0) (zero : input.proof.length = 0) :
    ∃ final : MachineState, Hop (sub.image .check) (sub.initialState .check input) final 5 5 ∧
      WrapExit sub input final := by
  obtain ⟨c₀, _, _, _, _, _, _, _, c₈, c₉, c₁₀, _⟩ := run_codes
  let init := sub.initialState .check input
  have run₀ := entry_hop wrap input
  let s₀ := init.setPC (BitVec.ofNat 64 (4096+4*(460+0)))
  have x16 : s₀.getReg .x16 = 0#64 := by
    show init.getReg .x16 = _; rw [loader_reg lay, empty]; rfl
  have x17 : init.getReg .x17 = 0#64 := by rw [loader_reg lay, zero]; rfl
  have run₁ := wrap_control wrap s₀ (.BEQ .x16 .x0 1236) 0 c₀ rfl rfl rfl
  rw [beq_shape, x16, show s₀.getReg .x0 = 0#64 from rfl] at run₁
  simp only [beq_self_eq_true, if_true] at run₁
  generalize h₁ : s₀.setPC (s₀.pc + signExtend13 1236) = s₁ at run₁
  have pc₁ : s₁.pc = BitVec.ofNat 64 (4096+4*(460+309)) := by rw [← h₁, set_pc_pc]; rfl
  have reg₁ (r : Reg) : s₁.getReg r = init.getReg r := by rw [← h₁, set_pc_reg]; rfl
  have run₂ := wrap_control wrap s₁ (.BNE .x17 .x0 12) 309 c₈ pc₁ rfl rfl
  rw [bne_shape, reg₁ .x17, x17, show s₁.getReg .x0 = 0#64 from rfl] at run₂
  simp only [bne_self_eq_false, Bool.false_eq_true, if_false] at run₂
  generalize h₂ : s₁.setPC (s₁.pc + 4) = s₂ at run₂
  have pc₂ : s₂.pc = BitVec.ofNat 64 (4096+4*(460+310)) := by rw [← h₂, set_pc_pc, pc₁]; rfl
  have pure₃ : ([.ADDI .x6 .x0 1424] : List Instr).all wrapPure = true := rfl
  have run₃ := wrap_pure_run wrap _ 310 s₂ c₉ pc₂ pure₃
  have pc₃ := wrap_pure_pc _ s₂ pure₃
  have x6₃ : (([.ADDI .x6 .x0 1424] : List Instr).foldl execInstrBr s₂).getReg .x6 = BitVec.ofNat 64 1424 := by
    have z : s₂.getReg .x0 = 0#64 := rfl
    simp [execInstrBr, get_reg_set_reg, z]; decide
  have keep₃ (r : Reg) (a : r ≠ .x6) : (([.ADDI .x6 .x0 1424] : List Instr).foldl execInstrBr s₂).getReg r = s₂.getReg r := by
    simp [execInstrBr, get_reg_set_reg, Ne.symm a]
  have mem₃ := wrap_pure_mem _ s₂ pure₃
  generalize h₃ : ([.ADDI .x6 .x0 1424] : List Instr).foldl execInstrBr s₂ = s₃ at run₃ pc₃ x6₃ keep₃ mem₃
  have run₄ := wrap_control wrap s₃ (.JAL .x0 2094072) 311 c₁₀ (by rw [pc₃, pc₂, pc_add]; rfl) rfl rfl
  obtain ⟨mem₄, reg₄⟩ := jal_keeps s₃ 2094072
  have pc₄ : (execInstrBr s₃ (.JAL .x0 2094072)).pc = BitVec.ofNat 64 4100 := by
    simp only [execInstrBr]
    show s₃.pc + signExtend21 2094072 = _
    rw [pc₃, pc₂, pc_add]; decide
  generalize h₄ : execInstrBr s₃ (.JAL .x0 2094072) = s₄ at run₄ mem₄ reg₄ pc₄
  have regs (r : Reg) (a : r ≠ .x6) : s₄.getReg r = init.getReg r := by
    rw [reg₄, keep₃ r a, ← h₂, set_pc_reg, reg₁]
  have exact : input.proof.length = capLength input.positions := by rw [zero]; unfold capLength; simp [empty]
  refine ⟨s₄, (run₀.trans (run₁.trans (run₂.trans (run₃.trans run₄)))).cast rfl (by simp [wrapCost,
      instructionCycles]), pc₄, by rw [reg₄, x6₃], ?_, ?_⟩
  · intro r ne
    have length : (expandInput input).proof.length = input.proof.length := by
      rw [zero]; exact (expand_proof_length _ _).trans (by rw [empty])
    rw [regs r ne, loader_reg lay, loader_reg lay, length]
    rfl
  · intro w hw side
    have memEq : s₄.mem = init.mem := by
      rw [mem₄, mem₃, ← h₂, set_pc_mem, ← h₁, set_pc_mem]; rfl
    rw [expanded_loader lay input exact w hw, view_of_mem memEq]
    unfold expandedTarget
    by_cases low : w < proofWord
    · rw [if_pos low]
    · rw [if_neg low, if_neg (by rw [empty]; omega)]
      obtain ⟨u, rfl⟩ : ∃ u, w = proofWord + u := ⟨w - proofWord, by omega⟩
      exact beyond_zero lay input u (by rw [zero]; omega) hw


/-! ### The wrapper as a whole -/

theorem hop_then_pure {img : Image} {s t : MachineState} {a c b : Nat} {r : Execution}
    (hop : Hop img s t a c) (rest : ∀ fuel, execute img (b+fuel) t false = pure r) :
    ∀ fuel, execute img ((a+b)+fuel) s false = pure (r.charge c 0) := by
  intro fuel
  rw [Nat.add_assoc, hop (b+fuel), rest fuel]
  simp

/-- Exact length: the wrapper reaches donor word 1 in the donor's post-word-0 state on the
expanded input (outside the scratch table). -/
theorem wrap_accept {sub : Submission} (lay : WrapLayout sub) (wrap : WrapImage (sub.image .check))
    (input : CheckInput) (exact : input.proof.length = capLength input.positions) :
    ∃ (final : MachineState) (steps cycles : Nat), steps ≤ 851*input.positions.card + 5000 ∧
      Hop (sub.image .check) (sub.initialState .check input) final steps cycles ∧ WrapExit sub input final := by
  have card := card_bound' input.positions
  by_cases empty : input.positions.card = 0
  · have zero : input.proof.length = 0 := by rw [exact]; unfold capLength; simp [empty]
    obtain ⟨final, run, exit⟩ := empty_run lay wrap input empty zero
    exact ⟨final, 5, 5, by omega, run, exit⟩
  · have admitted : input.proof.length ≤ 23890755584 := by rw [exact]; unfold capLength; simp [empty]; omega
    have run₀ := entry_hop wrap input
    obtain ⟨s₁, run₁, x30₁, mem₁, regs₁, pc₁⟩ := guard_run lay wrap input empty admitted
    rw [if_pos exact] at pc₁
    obtain ⟨s₂, run₂, at₂, pc₂⟩ := table_start lay wrap input s₁ pc₁ x30₁ mem₁ regs₁
    obtain ⟨s₃, run₃, at₃, pc₃⟩ := table_loop lay wrap input exact empty 55 le_rfl s₂ pc₂ at₂
    rw [if_pos rfl] at pc₃
    obtain ⟨s₄, run₄, at₄, pc₄⟩ := loop_start lay wrap input empty exact s₃ pc₃ at₃
    obtain ⟨s₅, run₅, at₅, pc₅⟩ := records_loop lay wrap input input.positions.card le_rfl s₄ empty pc₄ at₄
    rw [if_pos rfl] at pc₅
    rw [Nat.sub_self] at at₅
    obtain ⟨final, run₆, exit⟩ := restore_run lay wrap input exact s₅ pc₅ at₅
    exact ⟨final, _, _, by omega,
      run₀.trans (run₁.trans (run₂.trans (run₃.trans (run₄.trans (run₅.trans run₆))))), exit⟩

/-- Any other length: the wrapper halts with failure, without an oracle call. -/
theorem wrap_reject {sub : Submission} (lay : WrapLayout sub) (wrap : WrapImage (sub.image .check))
    (input : CheckInput) (admitted : input.proof.length ≤ 23890755584)
    (wrong : input.proof.length ≠ capLength input.positions) :
    ∃ (steps : Nat) (result : Execution), steps ≤ 20 ∧ result.exit = .failure ∧ result.oracleCalls = 0 ∧
      ∀ fuel, execute (sub.image .check) (steps+fuel) (sub.initialState .check input) false = pure result := by
  obtain ⟨c₀, _, _, _, _, _, _, _, c₈, _⟩ := run_codes
  have card := card_bound' input.positions
  have run₀ := entry_hop wrap input
  by_cases empty : input.positions.card = 0
  · have nonzero : input.proof.length ≠ 0 := by
      intro h; apply wrong; rw [h]; unfold capLength; simp [empty]
    let init := sub.initialState .check input
    let s₀ := init.setPC (BitVec.ofNat 64 (4096+4*(460+0)))
    have x16 : s₀.getReg .x16 = 0#64 := by
      show init.getReg .x16 = _; rw [loader_reg lay, empty]; rfl
    have x17 : init.getReg .x17 = BitVec.ofNat 64 input.proof.length := by rw [loader_reg lay]; rfl
    have run₁ := wrap_control wrap s₀ (.BEQ .x16 .x0 1236) 0 c₀ rfl rfl rfl
    rw [beq_shape, x16, show s₀.getReg .x0 = 0#64 from rfl] at run₁
    simp only [beq_self_eq_true, if_true] at run₁
    generalize h₁ : s₀.setPC (s₀.pc + signExtend13 1236) = s₁ at run₁
    have pc₁ : s₁.pc = BitVec.ofNat 64 (4096+4*(460+309)) := by rw [← h₁, set_pc_pc]; rfl
    have reg₁ (r : Reg) : s₁.getReg r = init.getReg r := by rw [← h₁, set_pc_reg]; rfl
    have run₂ := wrap_control wrap s₁ (.BNE .x17 .x0 12) 309 c₈ pc₁ rfl rfl
    rw [bne_shape, reg₁ .x17, x17, show s₁.getReg .x0 = 0#64 from rfl] at run₂
    have ne : (BitVec.ofNat 64 input.proof.length != 0#64) = true := by
      simpa using word_ne_zero _ nonzero (by omega)
    rw [ne, if_pos rfl] at run₂
    generalize h₂ : s₁.setPC (s₁.pc + signExtend13 12) = s₂ at run₂
    have pc₂ : s₂.pc = BitVec.ofNat 64 (4096+4*(460+312)) := by rw [← h₂, set_pc_pc, pc₁]; rfl
    obtain ⟨final, rest⟩ := reject_run wrap s₂ pc₂
    exact ⟨1+1+1+3, _, by omega, rfl, rfl, hop_then_pure (run₀.trans (run₁.trans run₂)) rest⟩
  · obtain ⟨s₁, run₁, _, _, _, pc₁⟩ := guard_run lay wrap input empty admitted
    rw [if_neg wrong] at pc₁
    obtain ⟨final, rest⟩ := reject_run wrap s₁ pc₁
    exact ⟨1+7+3, _, by omega, rfl, rfl, hop_then_pure (run₀.trans run₁) rest⟩

end TwoPermutationPrototype.PentaWrap
