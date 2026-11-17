import CommitGolfCandidate.Check

/-! Execution of the commitment image's leaf subroutine. The actual instruction
addresses and return address differ from the checker; the scratch transform is the
same. Every oracle reply is covered by the execution and resource proofs. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

theorem commit_fetch (state : MachineState) (index : Nat) (instruction : Instr)
    (indexBound : index < 200) (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * index))
    (decoded : ((submission.image .commit).code[index]?).bind decodeInstruction =
      some (.base instruction)) :
    fetch (submission.image .commit) state = some (.base instruction) := by
  have pcNat : state.pc.toNat = 4096 + 4 * index := by
    rw [pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    omega
  rw [fetch, pcNat, if_pos (by omega)]
  have quotient : (4096 + 4 * index - 4096) / 4 = index := by omega
  rw [quotient]
  cases h : (submission.image .commit).code[index]? with
  | none => simp [h] at decoded
  | some word => simpa [h] using decoded

/-- The syscall argument registers that the leaf prologue fixes once per leaf:
compression (x5=0, x13=0) of the 64 scratch bytes at 256 (x10, x11) into scratch (x12). -/
def CommitSyscallArgs (state : MachineState) : Prop :=
  state.getReg .x5 = 0 ∧ state.getReg .x10 = 256 ∧ state.getReg .x11 = 64 ∧
    state.getReg .x12 = 256 ∧ state.getReg .x13 = 0

/-- State after the compression reply overwrites the low half of scratch memory. -/
def commitCompressionState (state : MachineState) (answer : BitVec 256) : MachineState :=
  writeBits state 256 answer

/-- Instruction index of the first copy instruction of unrolled leaf block `j`. -/
def commitBlockIndex (j : Nat) : Nat := 89 + 10 * j

/-- The leaf compression call sites perform precisely one fixed-width oracle query.
Their arguments were set by the leaf prologue; the syscall costs eight cycles. The input
is the 64-byte scratch contents; every oracle reply is handled by the actual writer. -/
theorem commit_compression (state : MachineState) (j : Nat) (hj : j < 8)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * (commitBlockIndex j + 8)))
    (args : CommitSyscallArgs state) (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (1 + fuel) state allowCoins =
      (do let answer ← World.query (.inr (.inl (readBuffer state 256 64)))
          let result ← execute (submission.image .commit) fuel (commitCompressionState state answer) allowCoins
          return result.charge 8 1) := by
  have fetched : fetch (submission.image .commit) state = some (.base .ECALL) := by
    apply commit_fetch _ (commitBlockIndex j + 8) _ (by simp only [commitBlockIndex]; omega) pc
    interval_cases j <;> rfl
  obtain ⟨r5, r10, r11, r12, r13⟩ := args
  have input : oracleInput state = some (.inl (readBuffer state 256 64)) := by
    simp [oracleInput, r13, r10, r11, r12, COMPRESSION_INPUT_LENGTH, COMPRESSION_OUTPUT_LENGTH,
      rangeValid, MEMORY_BYTES]
    all_goals (rw [r13]; simp)
  rw [show 1 + fuel = fuel + 1 by omega]
  rw [execute, fetched, if_pos r5, input]
  simp [writeOracleAnswer, r12, commitCompressionState,
    oracleCycles, COMPRESSION_CYCLES, Execution.charge]
  rfl

/-- The syscall reply write advances to the next instruction. -/
theorem commit_compression_pc (state : MachineState) (answer : BitVec 256) :
    (commitCompressionState state answer).pc = state.pc + 4 := rfl

/-- Compression preserves every register. -/
theorem commit_compression_register (state : MachineState) (answer : BitVec 256) (reg : Reg) :
    (commitCompressionState state answer).getReg reg = state.getReg reg := by
  rw [commitCompressionState, writeBits_register]

private def commitLeafCopyInstructions : List Instr :=
  [.LD .x6 .x8 0, .SD .x21 .x6 32, .LD .x6 .x8 8, .SD .x21 .x6 40,
   .LD .x6 .x8 16, .SD .x21 .x6 48, .LD .x6 .x8 24, .SD .x21 .x6 56]

private def commitLeafCopyPrefix (state : MachineState) (count : Nat) : MachineState :=
  (commitLeafCopyInstructions.take count).foldl execInstrBr state

def commitLeafCopyState (state : MachineState) : MachineState := commitLeafCopyPrefix state 8

private theorem commit_copy_register (state : MachineState) (count : Nat) (bounded : count ≤ 8)
    (reg : Reg) (scratch : reg ≠ .x6) :
    (commitLeafCopyPrefix state count).getReg reg = state.getReg reg := by
  have memRegister (state : MachineState) (address value : Word) (reg : Reg) :
      (state.setMem address value).getReg reg = state.getReg reg := by cases reg <;> rfl
  interval_cases count <;>
    simp only [commitLeafCopyPrefix, commitLeafCopyInstructions, List.take, List.foldl, execInstrBr,
      MachineState.getReg_setPC, memRegister,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm scratch)]

theorem commit_leaf_copy_pc (state : MachineState) :
    (commitLeafCopyState state).pc = state.pc + 32 := by
  simp [commitLeafCopyState, commitLeafCopyPrefix, commitLeafCopyInstructions, execInstrBr,
    MachineState.setPC, BitVec.add_assoc]

private theorem commit_pc_advance (state : MachineState) (a b : Nat) (pc : state.pc = BitVec.ofNat 64 a) :
    state.pc + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  rw [pc, BitVec.ofNat_add]

private theorem commit_pc_advance' (state : MachineState) (a b c : Nat)
    (pc : state.pc = BitVec.ofNat 64 a) (sum : a + b = c) :
    state.pc + BitVec.ofNat 64 b = BitVec.ofNat 64 c := by
  rw [pc, ← BitVec.ofNat_add, sum]

set_option maxHeartbeats 8000000 in
/-- Copy the next 256-bit message block into the upper scratch half. -/
theorem commit_leaf_copy (state : MachineState) (j : Nat) (hj : j < 8)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * commitBlockIndex j))
    (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word : Fin 4,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (8 + fuel) state allowCoins =
      (do let result ← execute (submission.image .commit) fuel (commitLeafCopyState state) allowCoins
          return result.charge 8 0) := by
  apply execute_unit_steps (states := commitLeafCopyPrefix state)
  intro i hi
  refine ⟨.base ((commitLeafCopyInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · have prefixPC : (commitLeafCopyPrefix state i).pc =
        BitVec.ofNat 64 (4096 + 4 * (commitBlockIndex j + i)) := by
      have step : (commitLeafCopyPrefix state i).pc = state.pc + BitVec.ofNat 64 (4 * i) := by
        interval_cases i <;>
          simp [commitLeafCopyPrefix, commitLeafCopyInstructions, execInstrBr, MachineState.setPC,
            BitVec.add_assoc]
      rw [step, commit_pc_advance state _ (4 * i) pc]
      congr 1
      omega
    apply commit_fetch _ (commitBlockIndex j + i) _ (by simp only [commitBlockIndex]; omega) prefixPC
    interval_cases j <;> interval_cases i <;> rfl
  · have sourceReg := commit_copy_register state i (by omega) .x8 (by decide)
    have scratchReg := (commit_copy_register state i (by omega) .x21 (by decide)).trans scratch
    have s0 := sourceValid ⟨0, by decide⟩
    have s1 := sourceValid ⟨1, by decide⟩
    have s2 := sourceValid ⟨2, by decide⟩
    have s3 := sourceValid ⟨3, by decide⟩
    have valid : memoryArgumentsValid (commitLeafCopyPrefix state i)
        ((commitLeafCopyInstructions[i]?).getD .EBREAK) = true := by
      interval_cases i <;>
        simp only [commitLeafCopyInstructions, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.getD_some, memoryArgumentsValid, memAccess, sourceReg, scratchReg, signExtend12] <;>
        first | exact s0 | exact s1 | exact s2 | exact s3 | rfl
    interval_cases i <;>
      simp only [commitLeafCopyInstructions, List.getElem?_cons_zero,
        List.getElem?_cons_succ, Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep, valid, ↓reduceIte] <;> rfl
  · interval_cases i <;> rfl

/-- The block epilogue advances the source pointer to the next 256-bit block. -/
def commitLeafNextState (state : MachineState) : MachineState :=
  (state.setReg .x8 (state.getReg .x8 + 32)).setPC (state.pc + 4)

theorem commit_leaf_next (state : MachineState) (j : Nat) (hj : j < 8)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * (commitBlockIndex j + 9)))
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (1 + fuel) state allowCoins =
      (do let result ← execute (submission.image .commit) fuel (commitLeafNextState state) allowCoins
          return result.charge 1 0) := by
  have fetched : fetch (submission.image .commit) state = some (.base (.ADDI .x8 .x8 32)) := by
    apply commit_fetch _ (commitBlockIndex j + 9) _ (by simp only [commitBlockIndex]; omega) pc
    interval_cases j <;> rfl
  have stepped : ordinaryStep state (.base (.ADDI .x8 .x8 32)) = some (commitLeafNextState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, commitLeafNextState]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

/-- One leaf block: copy 32 bytes, compress, then advance the source pointer. -/
def commitLeafStepState (state : MachineState) (answer : BitVec 256) : MachineState :=
  commitLeafNextState (commitCompressionState (commitLeafCopyState state) answer)

theorem commit_leaf_block_pc (state : MachineState) (answer : BitVec 256) :
    (commitLeafStepState state answer).pc = state.pc + 40 := by
  change (commitCompressionState (commitLeafCopyState state) answer).pc + 4 = _
  rw [commit_compression_pc, commit_leaf_copy_pc, BitVec.add_assoc, BitVec.add_assoc]
  rfl

theorem commit_leaf_block (state : MachineState) (j : Nat) (hj : j < 8)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * commitBlockIndex j))
    (scratch : state.getReg .x21 = 256) (args : CommitSyscallArgs state)
    (sourceValid : ∀ word : Fin 4,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (10 + fuel) state allowCoins =
      (do let answer ← World.query (.inr (.inl (readBuffer (commitLeafCopyState state) 256 64)))
          let result ← execute (submission.image .commit) fuel (commitLeafStepState state answer) allowCoins
          return result.charge 17 1) := by
  have copyPC : (commitLeafCopyState state).pc =
      BitVec.ofNat 64 (4096 + 4 * (commitBlockIndex j + 8)) := by
    rw [commit_leaf_copy_pc]
    exact commit_pc_advance' state _ 32 _ pc (by simp only [commitBlockIndex]; omega)
  have copyArgs : CommitSyscallArgs (commitLeafCopyState state) := by
    obtain ⟨r5, r10, r11, r12, r13⟩ := args
    exact ⟨(commit_copy_register state 8 (by decide) .x5 (by decide)).trans r5,
      (commit_copy_register state 8 (by decide) .x10 (by decide)).trans r10,
      (commit_copy_register state 8 (by decide) .x11 (by decide)).trans r11,
      (commit_copy_register state 8 (by decide) .x12 (by decide)).trans r12,
      (commit_copy_register state 8 (by decide) .x13 (by decide)).trans r13⟩
  have compressionPC (answer : BitVec 256) :
      (commitCompressionState (commitLeafCopyState state) answer).pc =
        BitVec.ofNat 64 (4096 + 4 * (commitBlockIndex j + 9)) := by
    rw [commit_compression_pc]
    exact commit_pc_advance' _ _ 4 _ copyPC (by simp only [commitBlockIndex]; omega)
  rw [show 10 + fuel = 8 + (1 + (1 + fuel)) by omega, commit_leaf_copy state j hj pc scratch sourceValid,
    commit_compression _ j hj copyPC copyArgs]
  simp only [bind_assoc, pure_bind]
  apply congrArg (fun continuation =>
    (liftM (World.query (.inr (.inl (readBuffer (commitLeafCopyState state) 256 64)))) :
      OracleComp World (BitVec 256)) >>= continuation)
  funext answer
  rw [commit_leaf_next _ j hj (compressionPC answer)]
  simp [commitLeafStepState, Execution.charge, ← Nat.add_assoc]

/-- A leaf block writes only the copy scratch register x6 and the source pointer x8. -/
theorem commit_leaf_step_register (state : MachineState) (answer : BitVec 256) (reg : Reg)
    (not6 : reg ≠ .x6) (not8 : reg ≠ .x8) :
    (commitLeafStepState state answer).getReg reg = state.getReg reg := by
  simp only [commitLeafStepState, commitLeafNextState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not8)]
  exact (commit_compression_register _ answer reg).trans
    (commit_copy_register state 8 (by decide) reg not6)

/-- The prologue's syscall arguments survive every leaf block. -/
theorem commit_leaf_step_args (state : MachineState) (answer : BitVec 256)
    (args : CommitSyscallArgs state) : CommitSyscallArgs (commitLeafStepState state answer) := by
  obtain ⟨r5, r10, r11, r12, r13⟩ := args
  exact ⟨(commit_leaf_step_register state answer .x5 (by decide) (by decide)).trans r5,
    (commit_leaf_step_register state answer .x10 (by decide) (by decide)).trans r10,
    (commit_leaf_step_register state answer .x11 (by decide) (by decide)).trans r11,
    (commit_leaf_step_register state answer .x12 (by decide) (by decide)).trans r12,
    (commit_leaf_step_register state answer .x13 (by decide) (by decide)).trans r13⟩

/-- The next block has the advanced source pointer; the unused counter register,
scratch pointer and subroutine return address are unchanged. -/
theorem commit_leaf_block_registers (state : MachineState) (answer : BitVec 256) :
    (commitLeafStepState state answer).getReg .x8 = state.getReg .x8 + 32 ∧
    (commitLeafStepState state answer).getReg .x28 = state.getReg .x28 ∧
    (commitLeafStepState state answer).getReg .x21 = state.getReg .x21 ∧
    (commitLeafStepState state answer).getReg .x1 = state.getReg .x1 := by
  refine ⟨?_, commit_leaf_step_register state answer .x28 (by decide) (by decide),
    commit_leaf_step_register state answer .x21 (by decide) (by decide),
    commit_leaf_step_register state answer .x1 (by decide) (by decide)⟩
  simp only [commitLeafStepState, commitLeafNextState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_eq (by decide : Reg.x8 ≠ .x0)]
  rw [commit_compression_register _ answer .x8, commitLeafCopyState,
    commit_copy_register state 8 (by decide) .x8 (by decide)]

/-- A semantic unfolding of the actual unrolled blocks. Each block issues the exact
scratch query from the image and applies its byte-writing and pointer transitions. -/
def commitLeafLoop (state : MachineState) : Nat → OracleComp World MachineState
  | 0 => pure state
  | count + 1 => do
      let answer ← World.query (.inr (.inl (readBuffer (commitLeafCopyState state) 256 64)))
      commitLeafLoop (commitLeafStepState state answer) count

private theorem commit_block_pc_next (state : MachineState) (count : Nat) (bounded : count + 1 ≤ 8)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * commitBlockIndex (8 - (count + 1))))
    (answer : BitVec 256) :
    (commitLeafStepState state answer).pc =
      BitVec.ofNat 64 (4096 + 4 * commitBlockIndex (8 - count)) := by
  rw [commit_leaf_block_pc]
  exact commit_pc_advance' state _ 40 _ pc (by simp only [commitBlockIndex]; omega)

/-- Exact execution of the remaining unrolled leaf blocks for every possible sequence of
oracle replies. Each block uses 10 instructions and 17 cycles, and makes one query. -/
theorem commit_leaf_loop (state : MachineState) (count : Nat) (bounded : count ≤ 8)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * commitBlockIndex (8 - count)))
    (scratch : state.getReg .x21 = 256) (args : CommitSyscallArgs state)
    (sourceValid : ∀ word < 4 * count,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (10 * count + fuel) state allowCoins =
      (do let finished ← commitLeafLoop state count
          let result ← execute (submission.image .commit) fuel finished allowCoins
          return result.charge (17 * count) count) := by
  induction count generalizing state with
  | zero => simp [commitLeafLoop, Execution.charge]
  | succ count ih =>
    have currentValid (word : Fin 4) :
        accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word.val)) 8 = true :=
      sourceValid word.val (by omega)
    have nextValid (answer : BitVec 256) (word : Nat) (bound : word < 4 * count) :
        accessValid ((commitLeafStepState state answer).getReg .x8 +
          BitVec.ofNat 64 (8 * word)) 8 = true := by
      have valid := sourceValid (word + 4) (by omega)
      rw [(commit_leaf_block_registers state answer).1]
      have address : state.getReg .x8 + 32 + BitVec.ofNat 64 (8 * word) =
          state.getReg .x8 + BitVec.ofNat 64 (8 * (word + 4)) := by
        rw [show 8 * (word + 4) = 32 + 8 * word by omega, BitVec.ofNat_add, BitVec.add_assoc]
        rfl
      rw [address]
      exact valid
    rw [show 10 * (count + 1) + fuel = 10 + (10 * count + fuel) by omega,
      commit_leaf_block state (8 - (count + 1)) (by omega) pc scratch args currentValid]
    simp only [commitLeafLoop, bind_assoc]
    apply congrArg (fun continuation =>
      (liftM (World.query (.inr (.inl (readBuffer (commitLeafCopyState state) 256 64)))) :
        OracleComp World (BitVec 256)) >>= continuation)
    funext answer
    rw [ih _ (by omega) (commit_block_pc_next state count bounded pc answer)
      ((commit_leaf_block_registers state answer).2.2.1.trans scratch)
      (commit_leaf_step_args state answer args) (nextValid answer)]
    simp [Execution.charge, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- Every possible run of the remaining blocks preserves the return address and
reaches the actual JALR instruction. -/
theorem commit_leaf_loop_finished (state : MachineState) (count : Nat) (bounded : count ≤ 8)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * commitBlockIndex (8 - count)))
    (finished : MachineState)
    (reachable : finished ∈ support (commitLeafLoop state count)) :
    finished.getReg .x1 = state.getReg .x1 ∧ finished.pc = 4772 := by
  induction count generalizing state with
  | zero =>
    simp only [commitLeafLoop, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    exact ⟨rfl, pc⟩
  | succ count ih =>
    simp only [commitLeafLoop, mem_support_bind_iff] at reachable
    obtain ⟨answer, _, reached⟩ := reachable
    have remaining := ih _ (by omega) (commit_block_pc_next state count bounded pc answer) reached
    exact ⟨remaining.1.trans (commit_leaf_block_registers state answer).2.2.2, remaining.2⟩

/-- The leaf subroutine returns to its caller using the preserved link register. -/
theorem commit_leaf_return (state : MachineState) (pc : state.pc = 4772)
    (link : state.getReg .x1 = 4292) (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (1 + fuel) state allowCoins =
      (do let result ← execute (submission.image .commit) fuel (state.setPC 4292) allowCoins
          return result.charge 1 0) := by
  have fetched : fetch (submission.image .commit) state =
      some (.base (.JALR .x0 .x1 0)) := by
    apply commit_fetch _ 169 _ (by decide) pc
    rfl
  have stepped : ordinaryStep state (.base (.JALR .x0 .x1 0)) = some (state.setPC 4292) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      MachineState.setReg, link]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

private def commitLeafPrologueInstructions : List Instr :=
  [.ADDI .x5 .x0 0, .ADDI .x10 .x0 256, .ADDI .x11 .x0 64, .ADDI .x12 .x0 256, .ADDI .x13 .x0 0]

private def commitLeafProloguePrefix (state : MachineState) (count : Nat) : MachineState :=
  (commitLeafPrologueInstructions.take count).foldl execInstrBr state

/-- Block-entry state: the five constant syscall arguments are set. -/
def commitLeafEntry (state : MachineState) : MachineState := commitLeafProloguePrefix state 5

theorem commit_leaf_entry_register (state : MachineState) (reg : Reg)
    (preserved : reg ∉ [.x5, .x10, .x11, .x12, .x13, .x28]) :
    (commitLeafEntry state).getReg reg = state.getReg reg := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at preserved
  rcases preserved with ⟨not5, not10, not11, not12, not13, _⟩
  simp only [commitLeafEntry, commitLeafProloguePrefix, commitLeafPrologueInstructions, List.take,
    List.foldl, execInstrBr, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not5),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not10),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not11),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not12),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not13)]

theorem commit_leaf_entry_args (state : MachineState) : CommitSyscallArgs (commitLeafEntry state) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [commitLeafEntry, commitLeafProloguePrefix, commitLeafPrologueInstructions, execInstrBr,
      signExtend12, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
      MachineState.getReg_setReg_ne] <;> rfl

theorem commit_leaf_entry_memory (state : MachineState) :
    (commitLeafEntry state).mem = state.mem := rfl

set_option maxHeartbeats 800000 in
/-- Five prologue instructions set the syscall arguments. -/
theorem commit_leaf_prologue (state : MachineState) (pc : state.pc = 4432)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (5 + fuel) state allowCoins =
      (do let result ← execute (submission.image .commit) fuel (commitLeafEntry state) allowCoins
          return result.charge 5 0) := by
  apply execute_unit_steps (states := commitLeafProloguePrefix state)
  intro i hi
  refine ⟨.base ((commitLeafPrologueInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply commit_fetch _ (84 + i) _ (by omega)
    · interval_cases i <;>
        simp [commitLeafProloguePrefix, commitLeafPrologueInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i <;>
      simp [commitLeafProloguePrefix, commitLeafPrologueInstructions, ordinaryStep,
        memoryArgumentsValid, memAccess]
  · interval_cases i <;> rfl

theorem commit_leaf_entry_pc (state : MachineState) (pc : state.pc = 4432) :
    (commitLeafEntry state).pc = BitVec.ofNat 64 (4096 + 4 * commitBlockIndex (8 - 8)) := by
  simp [commitLeafEntry, commitLeafProloguePrefix, commitLeafPrologueInstructions, execInstrBr,
    MachineState.setPC, pc, commitBlockIndex]

/-- The full 2048-bit leaf-hashing subroutine: set the syscall arguments, process eight
unrolled blocks, and return to the leaf-digest store. All oracle replies are covered.
It takes 86 instructions, costs exactly 142 cycles, and makes eight queries. -/
theorem commit_leaf_subroutine (state : MachineState) (pc : state.pc = 4432)
    (link : state.getReg .x1 = 4292) (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word < 32,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (86 + fuel) state allowCoins =
      (do let finished ← commitLeafLoop (commitLeafEntry state) 8
          let result ← execute (submission.image .commit) fuel (finished.setPC 4292) allowCoins
          return result.charge 142 8) := by
  let initialized := commitLeafEntry state
  have initScratch : initialized.getReg .x21 = 256 :=
    (commit_leaf_entry_register state .x21 (by decide)).trans scratch
  have initSource : ∀ word < 4 * 8,
      accessValid (initialized.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true := by
    rw [commit_leaf_entry_register state .x8 (by decide)]
    exact sourceValid
  rw [show 86 + fuel = 5 + (10 * 8 + (1 + fuel)) by omega,
    commit_leaf_prologue state pc,
    commit_leaf_loop initialized 8 (by decide) (commit_leaf_entry_pc state pc)
      initScratch (commit_leaf_entry_args state) initSource]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro finished reachable
  have done := commit_leaf_loop_finished initialized 8 (by decide)
    (commit_leaf_entry_pc state pc) finished reachable
  have finalLink : finished.getReg .x1 = 4292 := by
    rw [done.1]
    exact (commit_leaf_entry_register state .x1 (by decide)).trans link
  rw [commit_leaf_return finished done.2 finalLink]
  simp [Execution.charge, ← Nat.add_assoc]

private theorem commit_leaf_block_preserves (state : MachineState) (answer : BitVec 256) (reg : Reg)
    (preserved : reg ∉ [.x5, .x6, .x8, .x10, .x11, .x12, .x13, .x28]) :
    (commitLeafStepState state answer).getReg reg = state.getReg reg := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at preserved
  rcases preserved with ⟨_, not6, not8, _, _, _, _, _⟩
  exact commit_leaf_step_register state answer reg not6 not8

/-- The complete hash preserves the position/path metadata, proof pointer, root
pointer, and scratch pointer. It consumes exactly 32 bytes per block from x8. -/
theorem commit_leaf_loop_registers (state : MachineState) (count : Nat) (finished : MachineState)
    (reachable : finished ∈ support (commitLeafLoop state count)) :
    finished.getReg .x8 = state.getReg .x8 + BitVec.ofNat 64 (32 * count) ∧
    ∀ reg ∉ [.x5, .x6, .x8, .x10, .x11, .x12, .x13, .x28],
      finished.getReg reg = state.getReg reg := by
  induction count generalizing state with
  | zero =>
    simp only [commitLeafLoop, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    simp
  | succ count ih =>
    simp only [commitLeafLoop, mem_support_bind_iff] at reachable
    obtain ⟨answer, _, reached⟩ := reachable
    have rest := ih _ reached
    constructor
    · rw [rest.1, (commit_leaf_block_registers state answer).1]
      rw [show 32 * (count + 1) = 32 + 32 * count by omega, BitVec.ofNat_add, BitVec.add_assoc]
      rfl
    · intro reg preserved
      exact (rest.2 reg preserved).trans (commit_leaf_block_preserves state answer reg preserved)

end CommitGolfCandidate
