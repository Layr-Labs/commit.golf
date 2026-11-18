import CommitGolfCandidate.NonceExpandRun

/-! One expansion instruction at a time. `NonceAt state word regs` says that the machine is at
check word `word` and that its registers are `regs`; each lemma runs one instruction of the
expansion and gives the next word and register file. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

structure NonceAt (state : MachineState) (word : Nat) (regs : Reg → Word) : Prop where
  pc : state.pc = BitVec.ofNat 64 (4096 + 4 * word)
  regs : ∀ reg, state.getReg reg = regs reg

/-- The decoded instruction here expansion word `word`. -/
abbrev NonceDecoded (word : Nat) (instruction : Instr) : Prop :=
  (nonceExpandWords[word - 445]?).bind decodeInstruction = some (.base instruction)

theorem nonce_pc_next (word : Nat) :
    BitVec.ofNat 64 (4096 + 4 * word) + 4 = BitVec.ofNat 64 (4096 + 4 * (word + 1)) := by
  rw [show 4096 + 4 * (word + 1) = (4096 + 4 * word) + 4 by omega]
  exact (BitVec.ofNat_add (4096 + 4 * word) 4).symm

theorem NonceAt.update {state : MachineState} {word : Nat} {regs : Reg → Word}
    (here : NonceAt state word regs) (rd : Reg) (value : Word) (nonzero : rd ≠ .x0) :
    NonceAt ((state.setReg rd value).setPC (state.pc + 4)) (word + 1)
      (Function.update regs rd value) := by
  refine ⟨?_, ?_⟩
  · show state.pc + 4 = _
    rw [here.pc, nonce_pc_next]
  · intro reg
    rw [MachineState.getReg_setPC]
    by_cases same : reg = rd
    · subst same
      rw [MachineState.getReg_setReg_eq nonzero, Function.update_self]
    · rw [MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm same), Function.update_of_ne same, here.regs]

theorem NonceAt.jump {state : MachineState} {word : Nat} {regs : Reg → Word}
    (here : NonceAt state word regs) (target : Nat) (pc : Word)
    (moved : pc = BitVec.ofNat 64 (4096 + 4 * target)) :
    NonceAt (state.setPC pc) target regs :=
  ⟨by show pc = _; exact moved, fun reg => by rw [MachineState.getReg_setPC, here.regs]⟩

theorem NonceAt.next {state : MachineState} {word : Nat} {regs : Reg → Word}
    (here : NonceAt state word regs) (next : MachineState) (pc : next.pc = state.pc + 4)
    (same : ∀ reg, next.getReg reg = state.getReg reg) : NonceAt next (word + 1) regs :=
  ⟨by rw [pc, here.pc, nonce_pc_next], fun reg => by rw [same, here.regs]⟩

/-- Forget the shape of an updated register file. -/
theorem NonceAt.fresh {state : MachineState} {word : Nat} {regs : Reg → Word} {rd : Reg} {value : Word}
    (here : NonceAt state word (Function.update regs rd value)) :
    ∃ later, NonceAt state word later ∧ later rd = value ∧ ∀ reg, reg ≠ rd → later reg = regs reg :=
  ⟨_, here, Function.update_self _ _ _, fun _ outside => Function.update_of_ne outside _ _⟩

/-- A register-writing instruction without memory access. -/
theorem nonce_step_alu {state : MachineState} {word : Nat} {regs : Reg → Word}
    (here : NonceAt state word regs) (instruction : Instr) (rd : Reg) (value : Word)
    (nonzero : rd ≠ .x0) (above : 445 ≤ word) (inside : word < 547)
    (decoded : NonceDecoded word instruction)
    (stepped : ordinaryStep state (.base instruction) = some (execInstrBr state instruction))
    (effect : execInstrBr state instruction = (state.setReg rd value).setPC (state.pc + 4)) :
    NonceExpandRuns state 1 (execInstrBr state instruction) ∧
      NonceAt (execInstrBr state instruction) (word + 1) (Function.update regs rd value) := by
  refine ⟨nonce_expand_exec state word instruction here.pc above inside decoded stepped, ?_⟩
  rw [effect]
  exact here.update rd value nonzero

theorem nonce_step_addi {state : MachineState} {word : Nat} {regs : Reg → Word}
    (here : NonceAt state word regs) (rd rs : Reg) (imm : BitVec 12) (nonzero : rd ≠ .x0)
    (above : 445 ≤ word) (inside : word < 547) (decoded : NonceDecoded word (.ADDI rd rs imm)) :
    NonceExpandRuns state 1 (execInstrBr state (.ADDI rd rs imm)) ∧
      NonceAt (execInstrBr state (.ADDI rd rs imm)) (word + 1)
        (Function.update regs rd (regs rs + signExtend12 imm)) :=
  nonce_step_alu here _ rd _ nonzero above inside decoded rfl (by rw [← here.regs]; rfl)

theorem nonce_step_andi {state : MachineState} {word : Nat} {regs : Reg → Word}
    (here : NonceAt state word regs) (rd rs : Reg) (imm : BitVec 12) (nonzero : rd ≠ .x0)
    (above : 445 ≤ word) (inside : word < 547) (decoded : NonceDecoded word (.ANDI rd rs imm)) :
    NonceExpandRuns state 1 (execInstrBr state (.ANDI rd rs imm)) ∧
      NonceAt (execInstrBr state (.ANDI rd rs imm)) (word + 1)
        (Function.update regs rd (regs rs &&& signExtend12 imm)) :=
  nonce_step_alu here _ rd _ nonzero above inside decoded rfl (by rw [← here.regs]; rfl)

theorem nonce_step_slli {state : MachineState} {word : Nat} {regs : Reg → Word}
    (here : NonceAt state word regs) (rd rs : Reg) (shamt : BitVec 6) (nonzero : rd ≠ .x0)
    (above : 445 ≤ word) (inside : word < 547) (decoded : NonceDecoded word (.SLLI rd rs shamt)) :
    NonceExpandRuns state 1 (execInstrBr state (.SLLI rd rs shamt)) ∧
      NonceAt (execInstrBr state (.SLLI rd rs shamt)) (word + 1)
        (Function.update regs rd (regs rs <<< shamt.toNat)) :=
  nonce_step_alu here _ rd _ nonzero above inside decoded rfl (by rw [← here.regs]; rfl)

theorem nonce_step_add {state : MachineState} {word : Nat} {regs : Reg → Word}
    (here : NonceAt state word regs) (rd left right : Reg) (nonzero : rd ≠ .x0)
    (above : 445 ≤ word) (inside : word < 547) (decoded : NonceDecoded word (.ADD rd left right)) :
    NonceExpandRuns state 1 (execInstrBr state (.ADD rd left right)) ∧
      NonceAt (execInstrBr state (.ADD rd left right)) (word + 1)
        (Function.update regs rd (regs left + regs right)) :=
  nonce_step_alu here _ rd _ nonzero above inside decoded rfl (by rw [← here.regs, ← here.regs]; rfl)

theorem nonce_step_sub {state : MachineState} {word : Nat} {regs : Reg → Word}
    (here : NonceAt state word regs) (rd left right : Reg) (nonzero : rd ≠ .x0)
    (above : 445 ≤ word) (inside : word < 547) (decoded : NonceDecoded word (.SUB rd left right)) :
    NonceExpandRuns state 1 (execInstrBr state (.SUB rd left right)) ∧
      NonceAt (execInstrBr state (.SUB rd left right)) (word + 1)
        (Function.update regs rd (regs left - regs right)) :=
  nonce_step_alu here _ rd _ nonzero above inside decoded rfl (by rw [← here.regs, ← here.regs]; rfl)

theorem nonce_step_mul {state : MachineState} {word : Nat} {regs : Reg → Word}
    (here : NonceAt state word regs) (rd left right : Reg) (nonzero : rd ≠ .x0)
    (above : 445 ≤ word) (inside : word < 547) (decoded : NonceDecoded word (.MUL rd left right)) :
    NonceExpandRuns state 1 (execInstrBr state (.MUL rd left right)) ∧
      NonceAt (execInstrBr state (.MUL rd left right)) (word + 1)
        (Function.update regs rd (regs left * regs right)) :=
  nonce_step_alu here _ rd _ nonzero above inside decoded rfl (by rw [← here.regs, ← here.regs]; rfl)

theorem nonce_step_remu {state : MachineState} {word : Nat} {regs : Reg → Word}
    (here : NonceAt state word regs) (rd left right : Reg) (nonzero : rd ≠ .x0)
    (above : 445 ≤ word) (inside : word < 547) (decoded : NonceDecoded word (.REMU rd left right)) :
    NonceExpandRuns state 1 (execInstrBr state (.REMU rd left right)) ∧
      NonceAt (execInstrBr state (.REMU rd left right)) (word + 1)
        (Function.update regs rd (rv64_remu (regs left) (regs right))) :=
  nonce_step_alu here _ rd _ nonzero above inside decoded rfl (by rw [← here.regs, ← here.regs]; rfl)

theorem nonce_step_divu {state : MachineState} {word : Nat} {regs : Reg → Word}
    (here : NonceAt state word regs) (rd left right : Reg) (nonzero : rd ≠ .x0)
    (above : 445 ≤ word) (inside : word < 547) (decoded : NonceDecoded word (.DIVU rd left right)) :
    NonceExpandRuns state 1 (execInstrBr state (.DIVU rd left right)) ∧
      NonceAt (execInstrBr state (.DIVU rd left right)) (word + 1)
        (Function.update regs rd (rv64_divu (regs left) (regs right))) :=
  nonce_step_alu here _ rd _ nonzero above inside decoded rfl (by rw [← here.regs, ← here.regs]; rfl)

theorem nonce_step_ld {state : MachineState} {word : Nat} {regs : Reg → Word}
    (here : NonceAt state word regs) (rd rs : Reg) (offset : BitVec 12) (nonzero : rd ≠ .x0)
    (above : 445 ≤ word) (inside : word < 547) (decoded : NonceDecoded word (.LD rd rs offset))
    (valid : accessValid (regs rs + signExtend12 offset) 8 = true) :
    NonceExpandRuns state 1 (execInstrBr state (.LD rd rs offset)) ∧
      NonceAt (execInstrBr state (.LD rd rs offset)) (word + 1)
        (Function.update regs rd (state.getMem (regs rs + signExtend12 offset))) := by
  apply nonce_step_alu here _ rd _ nonzero above inside decoded
  · simp only [ordinaryStep, memoryArgumentsValid, memAccess, here.regs, valid, ite_true]
  · rw [← here.regs]; rfl

theorem nonce_step_lhu {state : MachineState} {word : Nat} {regs : Reg → Word}
    (here : NonceAt state word regs) (rd rs : Reg) (offset : BitVec 12) (nonzero : rd ≠ .x0)
    (above : 445 ≤ word) (inside : word < 547) (decoded : NonceDecoded word (.LHU rd rs offset))
    (valid : accessValid (regs rs + signExtend12 offset) 2 = true) :
    NonceExpandRuns state 1 (execInstrBr state (.LHU rd rs offset)) ∧
      NonceAt (execInstrBr state (.LHU rd rs offset)) (word + 1)
        (Function.update regs rd ((state.getHalfword (regs rs + signExtend12 offset)).zeroExtend 64)) := by
  apply nonce_step_alu here _ rd _ nonzero above inside decoded
  · simp only [ordinaryStep, memoryArgumentsValid, memAccess, here.regs, valid, ite_true]
  · rw [← here.regs]; rfl

theorem nonce_step_sd {state : MachineState} {word : Nat} {regs : Reg → Word}
    (here : NonceAt state word regs) (base source : Reg) (offset : BitVec 12)
    (above : 445 ≤ word) (inside : word < 547) (decoded : NonceDecoded word (.SD base source offset))
    (valid : accessValid (regs base + signExtend12 offset) 8 = true) :
    NonceExpandRuns state 1 (execInstrBr state (.SD base source offset)) ∧
      NonceAt (execInstrBr state (.SD base source offset)) (word + 1) regs ∧
      execInstrBr state (.SD base source offset) =
        (state.setMem (regs base + signExtend12 offset) (regs source)).setPC (state.pc + 4) := by
  have stepped : ordinaryStep state (.base (.SD base source offset)) =
      some (execInstrBr state (.SD base source offset)) := by
    simp only [ordinaryStep, memoryArgumentsValid, memAccess, here.regs, valid, ite_true]
  have effect : execInstrBr state (.SD base source offset) =
      (state.setMem (regs base + signExtend12 offset) (regs source)).setPC (state.pc + 4) := by
    rw [← here.regs, ← here.regs]; rfl
  refine ⟨nonce_expand_exec state word _ here.pc above inside decoded stepped, ?_, effect⟩
  rw [effect]
  exact here.next _ rfl fun reg => by
    rw [MachineState.getReg_setPC]
    cases reg <;> rfl

theorem nonce_step_sh {state : MachineState} {word : Nat} {regs : Reg → Word}
    (here : NonceAt state word regs) (base source : Reg) (offset : BitVec 12)
    (above : 445 ≤ word) (inside : word < 547) (decoded : NonceDecoded word (.SH base source offset))
    (valid : accessValid (regs base + signExtend12 offset) 2 = true) :
    NonceExpandRuns state 1 (execInstrBr state (.SH base source offset)) ∧
      NonceAt (execInstrBr state (.SH base source offset)) (word + 1) regs ∧
      execInstrBr state (.SH base source offset) =
        (state.setHalfword (regs base + signExtend12 offset) ((regs source).truncate 16)).setPC
          (state.pc + 4) := by
  have stepped : ordinaryStep state (.base (.SH base source offset)) =
      some (execInstrBr state (.SH base source offset)) := by
    simp only [ordinaryStep, memoryArgumentsValid, memAccess, here.regs, valid, ite_true]
  have effect : execInstrBr state (.SH base source offset) =
      (state.setHalfword (regs base + signExtend12 offset) ((regs source).truncate 16)).setPC
        (state.pc + 4) := by
    rw [← here.regs, ← here.regs]; rfl
  refine ⟨nonce_expand_exec state word _ here.pc above inside decoded stepped, ?_, effect⟩
  rw [effect]
  exact here.next _ rfl fun reg => by
    rw [MachineState.getReg_setPC]
    cases reg <;> rfl

theorem nonce_sign_zero : signExtend12 (0 : BitVec 12) = 0 := rfl
theorem nonce_sign_zero' : signExtend12 0#12 = 0#64 := rfl

theorem nonce_add_zero (value : Word) : value + signExtend12 0 = value := by
  rw [show signExtend12 (0 : BitVec 12) = 0 from rfl]
  exact BitVec.add_zero value

theorem nonce_addi_mem (state : MachineState) (rd rs : Reg) (imm : BitVec 12) :
    (execInstrBr state (.ADDI rd rs imm)).mem = state.mem := by
  cases rd <;> rfl
theorem nonce_andi_mem (state : MachineState) (rd rs : Reg) (imm : BitVec 12) :
    (execInstrBr state (.ANDI rd rs imm)).mem = state.mem := by
  cases rd <;> rfl
theorem nonce_slli_mem (state : MachineState) (rd rs : Reg) (shamt : BitVec 6) :
    (execInstrBr state (.SLLI rd rs shamt)).mem = state.mem := by
  cases rd <;> rfl
theorem nonce_add_mem (state : MachineState) (rd left right : Reg) :
    (execInstrBr state (.ADD rd left right)).mem = state.mem := by
  cases rd <;> rfl
theorem nonce_sub_mem (state : MachineState) (rd left right : Reg) :
    (execInstrBr state (.SUB rd left right)).mem = state.mem := by
  cases rd <;> rfl
theorem nonce_mul_mem (state : MachineState) (rd left right : Reg) :
    (execInstrBr state (.MUL rd left right)).mem = state.mem := by
  cases rd <;> rfl
theorem nonce_remu_mem (state : MachineState) (rd left right : Reg) :
    (execInstrBr state (.REMU rd left right)).mem = state.mem := by
  cases rd <;> rfl
theorem nonce_divu_mem (state : MachineState) (rd left right : Reg) :
    (execInstrBr state (.DIVU rd left right)).mem = state.mem := by
  cases rd <;> rfl
theorem nonce_ld_mem (state : MachineState) (rd rs : Reg) (offset : BitVec 12) :
    (execInstrBr state (.LD rd rs offset)).mem = state.mem := by
  cases rd <;> rfl
theorem nonce_lhu_mem (state : MachineState) (rd rs : Reg) (offset : BitVec 12) :
    (execInstrBr state (.LHU rd rs offset)).mem = state.mem := by
  cases rd <;> rfl
theorem nonce_jal_mem (state : MachineState) (rd : Reg) (offset : BitVec 21) :
    (execInstrBr state (.JAL rd offset)).mem = state.mem := by
  cases rd <;> rfl
theorem nonce_jalr_mem (state : MachineState) (rd rs : Reg) (offset : BitVec 12) :
    (execInstrBr state (.JALR rd rs offset)).mem = state.mem := by
  cases rd <;> rfl

theorem nonce_beq_mem (state : MachineState) (left right : Reg) (offset : BitVec 13) :
    (execInstrBr state (.BEQ left right offset)).mem = state.mem := by
  simp only [execInstrBr]
  split <;> rfl

theorem nonce_bne_mem (state : MachineState) (left right : Reg) (offset : BitVec 13) :
    (execInstrBr state (.BNE left right offset)).mem = state.mem := by
  simp only [execInstrBr]
  split <;> rfl

theorem nonce_bltu_mem (state : MachineState) (left right : Reg) (offset : BitVec 13) :
    (execInstrBr state (.BLTU left right offset)).mem = state.mem := by
  simp only [execInstrBr]
  split <;> rfl

/-- A conditional branch to word `target` when `taken`. -/
theorem nonce_step_branch {state : MachineState} {word : Nat} {regs : Reg → Word}
    (here : NonceAt state word regs) (instruction : Instr) (target : Nat) (taken : Bool)
    (above : 445 ≤ word) (inside : word < 547) (decoded : NonceDecoded word instruction)
    (stepped : ordinaryStep state (.base instruction) = some (execInstrBr state instruction))
    (effect : execInstrBr state instruction =
      state.setPC (if taken then BitVec.ofNat 64 (4096 + 4 * target) else state.pc + 4)) :
    NonceExpandRuns state 1 (execInstrBr state instruction) ∧
      NonceAt (execInstrBr state instruction) (if taken then target else word + 1) regs := by
  refine ⟨nonce_expand_exec state word instruction here.pc above inside decoded stepped, ?_⟩
  rw [effect]
  cases taken
  · exact here.jump _ _ (by rw [if_neg (by decide), here.pc, nonce_pc_next]; rfl)
  · exact here.jump _ _ (by rw [if_pos rfl]; rfl)

theorem nonce_step_beq {state : MachineState} {word : Nat} {regs : Reg → Word}
    (here : NonceAt state word regs) (left right : Reg) (offset : BitVec 13) (target : Nat)
    (above : 445 ≤ word) (inside : word < 547) (decoded : NonceDecoded word (.BEQ left right offset))
    (moved : BitVec.ofNat 64 (4096 + 4 * word) + signExtend13 offset = BitVec.ofNat 64 (4096 + 4 * target)) :
    NonceExpandRuns state 1 (execInstrBr state (.BEQ left right offset)) ∧
      NonceAt (execInstrBr state (.BEQ left right offset))
        (if regs left = regs right then target else word + 1) regs := by
  have result := nonce_step_branch here (.BEQ left right offset) target (decide (regs left = regs right))
    above inside decoded rfl (by
      simp only [execInstrBr, here.regs, here.pc, ← moved]
      by_cases same : regs left = regs right <;> simp [same])
  simpa only [decide_eq_true_eq] using result

theorem nonce_step_bne {state : MachineState} {word : Nat} {regs : Reg → Word}
    (here : NonceAt state word regs) (left right : Reg) (offset : BitVec 13) (target : Nat)
    (above : 445 ≤ word) (inside : word < 547) (decoded : NonceDecoded word (.BNE left right offset))
    (moved : BitVec.ofNat 64 (4096 + 4 * word) + signExtend13 offset = BitVec.ofNat 64 (4096 + 4 * target)) :
    NonceExpandRuns state 1 (execInstrBr state (.BNE left right offset)) ∧
      NonceAt (execInstrBr state (.BNE left right offset))
        (if regs left = regs right then word + 1 else target) regs := by
  have result := nonce_step_branch here (.BNE left right offset) target (!decide (regs left = regs right))
    above inside decoded rfl (by
      simp only [execInstrBr, here.regs, here.pc, ← moved]
      by_cases same : regs left = regs right <;> simp [same])
  by_cases same : regs left = regs right <;> simpa [same] using result

theorem nonce_step_bltu {state : MachineState} {word : Nat} {regs : Reg → Word}
    (here : NonceAt state word regs) (left right : Reg) (offset : BitVec 13) (target : Nat)
    (above : 445 ≤ word) (inside : word < 547) (decoded : NonceDecoded word (.BLTU left right offset))
    (moved : BitVec.ofNat 64 (4096 + 4 * word) + signExtend13 offset = BitVec.ofNat 64 (4096 + 4 * target)) :
    NonceExpandRuns state 1 (execInstrBr state (.BLTU left right offset)) ∧
      NonceAt (execInstrBr state (.BLTU left right offset))
        (if (regs left).toNat < (regs right).toNat then target else word + 1) regs := by
  have result := nonce_step_branch here (.BLTU left right offset) target
    (decide ((regs left).toNat < (regs right).toNat)) above inside decoded rfl (by
      simp only [execInstrBr, here.regs, here.pc, ← moved, BitVec.ult]
      by_cases less : (regs left).toNat < (regs right).toNat <;> simp [less])
  simpa only [decide_eq_true_eq] using result

/-- `jal rd, offset` to word `target`, linking word `word + 1` when `rd ≠ x0`. -/
theorem nonce_step_jal {state : MachineState} {word : Nat} {regs : Reg → Word}
    (here : NonceAt state word regs) (rd : Reg) (offset : BitVec 21) (target : Nat)
    (above : 445 ≤ word) (inside : word < 547) (decoded : NonceDecoded word (.JAL rd offset))
    (moved : BitVec.ofNat 64 (4096 + 4 * word) + signExtend21 offset = BitVec.ofNat 64 (4096 + 4 * target)) :
    NonceExpandRuns state 1 (execInstrBr state (.JAL rd offset)) ∧
      NonceAt (execInstrBr state (.JAL rd offset)) target
        (if rd = .x0 then regs else Function.update regs rd (BitVec.ofNat 64 (4096 + 4 * (word + 1)))) := by
  refine ⟨nonce_expand_exec state word _ here.pc above inside decoded rfl, ?_⟩
  refine ⟨?_, ?_⟩
  · show state.pc + signExtend21 offset = _
    rw [here.pc, moved]
  · intro reg
    change ((state.setReg rd (state.pc + 4)).setPC (state.pc + signExtend21 offset)).getReg reg = _
    rw [MachineState.getReg_setPC]
    by_cases zero : rd = .x0
    · subst zero
      rw [if_pos rfl]
      exact here.regs reg
    · rw [if_neg zero]
      by_cases same : reg = rd
      · subst same
        rw [MachineState.getReg_setReg_eq zero, Function.update_self, here.pc, nonce_pc_next]
      · rw [MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm same), Function.update_of_ne same, here.regs]

/-- `jalr x0, 0(x1)` back to word `target`. -/
theorem nonce_step_ret {state : MachineState} {word : Nat} {regs : Reg → Word}
    (here : NonceAt state word regs) (target : Nat) (small : 4096 + 4 * target < 2 ^ 64)
    (above : 445 ≤ word) (inside : word < 547) (decoded : NonceDecoded word (.JALR .x0 .x1 0))
    (link : regs .x1 = BitVec.ofNat 64 (4096 + 4 * target))
    (masked : (BitVec.ofNat 64 (4096 + 4 * target) + signExtend12 0) &&& ~~~1#64 =
      BitVec.ofNat 64 (4096 + 4 * target)) :
    NonceExpandRuns state 1 (execInstrBr state (.JALR .x0 .x1 0)) ∧
      NonceAt (execInstrBr state (.JALR .x0 .x1 0)) target regs := by
  refine ⟨nonce_expand_exec state word _ here.pc above inside decoded rfl, ?_⟩
  apply here.jump
  show (state.getReg .x1 + signExtend12 0) &&& ~~~1#64 = _
  rw [here.regs, link, masked]

end CommitGolfCandidate
