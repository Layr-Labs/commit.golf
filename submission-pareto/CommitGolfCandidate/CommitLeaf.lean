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

/-- The syscall arguments installed once by the commitment image before the leaf loop. -/
structure CommitCompressionArgs (state : MachineState) : Prop where
  selector : state.getReg .x5 = 0
  input : state.getReg .x10 = 256
  length : state.getReg .x11 = 64
  output : state.getReg .x12 = 256
  salt : state.getReg .x13 = 0

/-- State after the compression reply overwrites the low half of scratch memory. -/
def commitCompressionState (state : MachineState) (answer : BitVec 256) : MachineState :=
  writeBits state 256 answer

/-- The block compression call sites perform exactly one fixed-width oracle query each.
The syscall costs eight cycles. Its arguments were hoisted out of the loop, and the
eight call sites are at consecutive 40-byte blocks. -/
theorem commit_compression (b : Fin 8) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (4488 + 40 * b.val))
    (args : CommitCompressionArgs state) (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (1 + fuel) state allowCoins =
      (do let answer ← World.query (.inr (.inl (readBuffer state 256 64)))
          let result ← execute (submission.image .commit) fuel (commitCompressionState state answer) allowCoins
          return result.charge 8 1) := by
  have fetched : fetch (submission.image .commit) state = some (.base .ECALL) := by
    have pc' : state.pc = BitVec.ofNat 64 (4096 + 4 * (98 + 10 * b.val)) := by
      rw [pc]
      congr 1
      omega
    apply commit_fetch _ (98 + 10 * b.val) _ (by omega) pc'
    fin_cases b <;> rfl
  have kind : (state.getReg .x13).toNat = 0 := by simpa [args.salt]
  have input : oracleInput state = some (.inl (readBuffer state 256 64)) := by
    unfold oracleInput
    rw [kind]
    simp [args.output, args.input, args.length, COMPRESSION_INPUT_LENGTH,
      COMPRESSION_OUTPUT_LENGTH, rangeValid, MEMORY_BYTES]
  rw [Nat.add_comm 1 fuel, execute, fetched, if_pos args.selector, input]
  simp [writeOracleAnswer, args.output, commitCompressionState,
    oracleCycles, COMPRESSION_CYCLES, Execution.charge]
  rfl

/-- The reply write advances to the next instruction. -/
theorem commit_compression_pc (state : MachineState) (answer : BitVec 256) :
    (commitCompressionState state answer).pc = state.pc + 4 := by
  simp [commitCompressionState, writeBits, MachineState.setPC, BitVec.add_assoc]

/-- Compression changes no registers at all; its arguments are already installed. -/
theorem commit_compression_register (state : MachineState) (answer : BitVec 256) (reg : Reg) :
    (commitCompressionState state answer).getReg reg = state.getReg reg := by
  simp [commitCompressionState, writeBits_register]

theorem commit_compression_args (state : MachineState) (answer : BitVec 256)
    (args : CommitCompressionArgs state) : CommitCompressionArgs (commitCompressionState state answer) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [commit_compression_register] using args.selector
  · simpa [commit_compression_register] using args.input
  · simpa [commit_compression_register] using args.length
  · simpa [commit_compression_register] using args.output
  · simpa [commit_compression_register] using args.salt

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

private theorem commit_leaf_copy_prefix_pc (state : MachineState) (count : Nat) (bounded : count ≤ 8) :
    (commitLeafCopyPrefix state count).pc = state.pc + BitVec.ofNat 64 (4 * count) := by
  interval_cases count <;>
    simp [commitLeafCopyPrefix, commitLeafCopyInstructions, execInstrBr, MachineState.setPC,
      BitVec.add_assoc]

set_option maxHeartbeats 800000 in
/-- Copy the next 256-bit message block into the upper scratch half. -/
theorem commit_leaf_copy (b : Fin 8) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (4456 + 40 * b.val))
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
  · have prefixPC : (commitLeafCopyPrefix state i).pc = state.pc + BitVec.ofNat 64 (4 * i) :=
      commit_leaf_copy_prefix_pc state i (by omega)
    have pc' : (commitLeafCopyPrefix state i).pc =
        BitVec.ofNat 64 (4096 + 4 * (90 + 10 * b.val + i)) := by
      rw [prefixPC, pc, ← BitVec.ofNat_add]
      congr 1
      omega
    apply commit_fetch _ (90 + 10 * b.val + i) _ (by omega) pc'
    fin_cases b <;> interval_cases i <;> rfl
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

/-- The unrolled leaf blocks advance the message pointer by one block. The vestigial
counter initialization at leaf entry is never read, and x28 is preserved. -/
def commitLeafAdvanceState (state : MachineState) : MachineState :=
  (state.setReg .x8 (state.getReg .x8 + 32)).setPC (state.pc + 4)

theorem commit_leaf_advance (b : Fin 8) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (4492 + 40 * b.val))
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (1 + fuel) state allowCoins =
      (do let result ← execute (submission.image .commit) fuel (commitLeafAdvanceState state) allowCoins
          return result.charge 1 0) := by
  have fetched : fetch (submission.image .commit) state = some (.base (.ADDI .x8 .x8 32)) := by
    have pc' : state.pc = BitVec.ofNat 64 (4096 + 4 * (99 + 10 * b.val)) := by
      rw [pc]
      congr 1
      omega
    apply commit_fetch _ (99 + 10 * b.val) _ (by omega) pc'
    fin_cases b <;> rfl
  have stepped : ordinaryStep state (.base (.ADDI .x8 .x8 32)) = some (commitLeafAdvanceState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      commitLeafAdvanceState, MachineState.setPC, BitVec.add_assoc]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

/-- One leaf block: copy 32 bytes, compress, then advance the pointer. -/
def commitLeafStepState (state : MachineState) (answer : BitVec 256) : MachineState :=
  commitLeafAdvanceState (commitCompressionState (commitLeafCopyState state) answer)

theorem commit_leaf_block (b : Fin 8) (state : MachineState)
    (pc : state.pc = BitVec.ofNat 64 (4456 + 40 * b.val))
    (scratch : state.getReg .x21 = 256) (args : CommitCompressionArgs state)
    (sourceValid : ∀ word : Fin 4,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (10 + fuel) state allowCoins =
      (do let answer ← World.query (.inr (.inl (readBuffer (commitLeafCopyState state) 256 64)))
          let result ← execute (submission.image .commit) fuel (commitLeafStepState state answer) allowCoins
          return result.charge 17 1) := by
  have copyPC : (commitLeafCopyState state).pc = BitVec.ofNat 64 (4488 + 40 * b.val) := by
    change (commitLeafCopyPrefix state 8).pc = _
    rw [commit_leaf_copy_prefix_pc state 8 (by decide), pc, ← BitVec.ofNat_add]
    congr 1
    omega
  have copyReg (reg : Reg) (not6 : reg ≠ .x6) :
      (commitLeafCopyState state).getReg reg = state.getReg reg :=
    commit_copy_register state 8 (by decide) reg not6
  have copyScratch : (commitLeafCopyState state).getReg .x21 = 256 := (copyReg .x21 (by decide)).trans scratch
  have copyArgs : CommitCompressionArgs (commitLeafCopyState state) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact (copyReg .x5 (by decide)).trans args.selector
    · exact (copyReg .x10 (by decide)).trans args.input
    · exact (copyReg .x11 (by decide)).trans args.length
    · exact (copyReg .x12 (by decide)).trans args.output
    · exact (copyReg .x13 (by decide)).trans args.salt
  have compressionPC (answer : BitVec 256) :
      (commitCompressionState (commitLeafCopyState state) answer).pc =
        BitVec.ofNat 64 (4492 + 40 * b.val) := by
    rw [commit_compression_pc, copyPC]
    change BitVec.ofNat 64 (4488 + 40 * b.val) + BitVec.ofNat 64 4 =
      BitVec.ofNat 64 (4492 + 40 * b.val)
    rw [← BitVec.ofNat_add]
    congr 1
    omega
  rw [show 10 + fuel = 8 + (1 + (1 + fuel)) by omega,
    commit_leaf_copy b state pc scratch sourceValid,
    commit_compression b (commitLeafCopyState state) copyPC copyArgs]
  simp only [bind_assoc, pure_bind]
  apply congrArg (fun continuation =>
    (liftM (World.query (.inr (.inl (readBuffer (commitLeafCopyState state) 256 64)))) :
      OracleComp World (BitVec 256)) >>= continuation)
  funext answer
  rw [commit_leaf_advance b _ (compressionPC answer)]
  simp [commitLeafStepState, Execution.charge, ← Nat.add_assoc]

/-- A block advances the source pointer by one digest; all other registers, including
the vestigial block counter, are unchanged. -/
theorem commit_leaf_block_registers (state : MachineState) (answer : BitVec 256) :
    (commitLeafStepState state answer).getReg .x8 = state.getReg .x8 + 32 ∧
    (commitLeafStepState state answer).getReg .x21 = state.getReg .x21 ∧
    (commitLeafStepState state answer).getReg .x1 = state.getReg .x1 := by
  have preserved (reg : Reg) (not6 : reg ≠ .x6) :
      (commitCompressionState (commitLeafCopyState state) answer).getReg reg = state.getReg reg :=
    (commit_compression_register _ answer reg).trans
      (commit_copy_register state 8 (by decide) reg not6)
  simp only [commitLeafStepState, commitLeafAdvanceState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_eq (by decide : Reg.x8 ≠ .x0),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x8 ≠ .x21),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x8 ≠ .x1)]
  rw [preserved .x8 (by decide), preserved .x21 (by decide), preserved .x1 (by decide)]
  exact ⟨rfl, rfl, rfl⟩

/-- Copy (32 bytes), compression reply (4 bytes) and pointer advance (4 bytes) move
the program counter forward by exactly one 40-byte block. -/
theorem commit_leaf_block_pc (state : MachineState) (answer : BitVec 256) :
    (commitLeafStepState state answer).pc = state.pc + 40 := by
  simp only [commitLeafStepState, commitLeafAdvanceState, MachineState.setPC]
  rw [commit_compression_pc]
  change (commitLeafCopyPrefix state 8).pc + 4 + 4 = state.pc + 40
  rw [commit_leaf_copy_prefix_pc state 8 (by decide)]
  simp [BitVec.add_assoc]

/-- A semantic unfolding of the actual block loop. Each iteration issues the exact
scratch query from the image and applies its byte-writing and pointer transitions. -/
def commitLeafLoop (state : MachineState) : Nat → OracleComp World MachineState
  | 0 => pure state
  | count + 1 => do
      let answer ← World.query (.inr (.inl (readBuffer (commitLeafCopyState state) 256 64)))
      commitLeafLoop (commitLeafStepState state answer) count

/-- Exact execution of the leaf hash loop for every possible sequence of oracle replies.
The unrolled loop uses ten instructions, 17 cycles and one query per block. -/
theorem commit_leaf_loop (state : MachineState) (block count : Nat) (bounded : block + count ≤ 8)
    (pc : 0 < count → state.pc = BitVec.ofNat 64 (4456 + 40 * block))
    (scratch : state.getReg .x21 = 256) (args : CommitCompressionArgs state)
    (sourceValid : ∀ word < 4 * count,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (10 * count + fuel) state allowCoins =
      (do let finished ← commitLeafLoop state count
          let result ← execute (submission.image .commit) fuel finished allowCoins
          return result.charge (17 * count) count) := by
  induction count generalizing state block with
  | zero => simp [commitLeafLoop, Execution.charge]
  | succ count ih =>
    have currentValid (word : Fin 4) :
        accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word.val)) 8 = true :=
      sourceValid word.val (by omega)
    let b : Fin 8 := ⟨block, by omega⟩
    have blockPC : state.pc = BitVec.ofNat 64 (4456 + 40 * b.val) := by
      simpa [b] using pc (by omega)
    have nextPC (answer : BitVec 256) (positive : 0 < count) :
        (commitLeafStepState state answer).pc =
          BitVec.ofNat 64 (4456 + 40 * (block + 1)) := by
      rw [commit_leaf_block_pc, pc (by omega)]
      change BitVec.ofNat 64 (4456 + 40 * block) + BitVec.ofNat 64 40 =
        BitVec.ofNat 64 (4456 + 40 * (block + 1))
      rw [← BitVec.ofNat_add]
      congr 1
    have stepReg (answer : BitVec 256) (reg : Reg) (not6 : reg ≠ .x6) (not8 : reg ≠ .x8) :
        (commitLeafStepState state answer).getReg reg = state.getReg reg := by
      simp only [commitLeafStepState, commitLeafAdvanceState, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not8)]
      exact (commit_compression_register _ answer reg).trans
        (commit_copy_register state 8 (by decide) reg not6)
    have nextArgs (answer : BitVec 256) : CommitCompressionArgs (commitLeafStepState state answer) := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact (stepReg answer .x5 (by decide) (by decide)).trans args.selector
      · exact (stepReg answer .x10 (by decide) (by decide)).trans args.input
      · exact (stepReg answer .x11 (by decide) (by decide)).trans args.length
      · exact (stepReg answer .x12 (by decide) (by decide)).trans args.output
      · exact (stepReg answer .x13 (by decide) (by decide)).trans args.salt
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
      commit_leaf_block b state blockPC scratch args currentValid]
    simp only [commitLeafLoop, bind_assoc]
    apply congrArg (fun continuation =>
      (liftM (World.query (.inr (.inl (readBuffer (commitLeafCopyState state) 256 64)))) :
        OracleComp World (BitVec 256)) >>= continuation)
    funext answer
    rw [ih _ (block + 1) (by omega) (nextPC answer)
      ((commit_leaf_block_registers state answer).2.1.trans scratch) (nextArgs answer)
      (nextValid answer)]
    simp [Execution.charge, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- Every possible run of the bounded loop preserves the return address and leaves
the program counter exactly one block past its entry. -/
theorem commit_leaf_loop_finished (state : MachineState) (block count : Nat)
    (bounded : block + count ≤ 8) (finished : MachineState)
    (reachable : finished ∈ support (commitLeafLoop state count)) :
    finished.getReg .x1 = state.getReg .x1 ∧
      (0 < count → finished.pc = state.pc + BitVec.ofNat 64 (40 * count)) := by
  induction count generalizing state block finished with
  | zero =>
    simp only [commitLeafLoop, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    exact ⟨rfl, by omega⟩
  | succ count ih =>
    simp only [commitLeafLoop, mem_support_bind_iff] at reachable
    obtain ⟨answer, _, reached⟩ := reachable
    change BitVec 256 at answer
    have remaining := ih _ (block + 1) (by omega) _ reached
    refine ⟨remaining.1.trans (commit_leaf_block_registers state answer).2.2, ?_⟩
    intro _
    by_cases empty : count = 0
    · subst count
      simp only [commitLeafLoop, support_pure, Set.mem_singleton_iff] at reached
      subst finished
      rw [commit_leaf_block_pc]
      rfl
    · rw [remaining.2 (Nat.pos_of_ne_zero empty), commit_leaf_block_pc, BitVec.add_assoc]
      apply congrArg (fun x : BitVec 64 => state.pc + x)
      change (40 : BitVec 64) + BitVec.ofNat 64 (40 * count) =
        BitVec.ofNat 64 (40 * (count + 1))
      rw [show (40 : BitVec 64) = BitVec.ofNat 64 40 by rfl, ← BitVec.ofNat_add]
      congr 1
      omega

/-- The leaf subroutine returns to its caller using the preserved link register. -/
theorem commit_leaf_return (state : MachineState) (pc : state.pc = 4776)
    (link : state.getReg .x1 = 4312) (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (1 + fuel) state allowCoins =
      (do let result ← execute (submission.image .commit) fuel (state.setPC 4312) allowCoins
          return result.charge 1 0) := by
  have fetched : fetch (submission.image .commit) state =
      some (.base (.JALR .x0 .x1 0)) := by
    apply commit_fetch _ 170 _ (by decide) pc
    rfl
  have stepped : ordinaryStep state (.base (.JALR .x0 .x1 0)) = some (state.setPC 4312) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      MachineState.setReg, link]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

/-- The full 2048-bit leaf-hashing subroutine: initialize eight blocks, process them
in eight straight-line blocks, and return to the leaf-digest store. All oracle replies
are covered. It takes 82 instructions, costs exactly 138 cycles, and makes eight queries. -/
theorem commit_leaf_subroutine (state : MachineState) (pc : state.pc = 4452)
    (link : state.getReg .x1 = 4312) (scratch : state.getReg .x21 = 256)
    (args : CommitCompressionArgs state)
    (sourceValid : ∀ word < 32,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (82 + fuel) state allowCoins =
      (do let finished ← commitLeafLoop ((state.setReg .x28 8).setPC 4456) 8
          let result ← execute (submission.image .commit) fuel (finished.setPC 4312) allowCoins
          return result.charge 138 8) := by
  let initialized := (state.setReg .x28 8).setPC 4456
  have fetched : fetch (submission.image .commit) state =
      some (.base (.ADDI .x28 .x0 8)) := by
    apply commit_fetch _ 89 _ (by decide) pc
    rfl
  have stepped : ordinaryStep state (.base (.ADDI .x28 .x0 8)) = some initialized := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      initialized, pc, MachineState.getReg]
  have initScratch : initialized.getReg .x21 = 256 := by
    simpa [initialized, MachineState.getReg_setPC, MachineState.getReg_setReg_ne] using scratch
  have initSource : ∀ word < 4 * 8,
      accessValid (initialized.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true := by
    simpa [initialized, MachineState.getReg_setPC, MachineState.getReg_setReg_ne] using sourceValid
  have initArgs : CommitCompressionArgs initialized := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa [initialized, MachineState.getReg_setPC, MachineState.getReg_setReg_ne] using args.selector
    · simpa [initialized, MachineState.getReg_setPC, MachineState.getReg_setReg_ne] using args.input
    · simpa [initialized, MachineState.getReg_setPC, MachineState.getReg_setReg_ne] using args.length
    · simpa [initialized, MachineState.getReg_setPC, MachineState.getReg_setReg_ne] using args.output
    · simpa [initialized, MachineState.getReg_setPC, MachineState.getReg_setReg_ne] using args.salt
  rw [show 82 + fuel = (10 * 8 + (1 + fuel)) + 1 by omega,
    execute_ordinary_step _ _ _ _ _ _ fetched stepped,
    commit_leaf_loop initialized 0 8 (by decide) (fun _ => rfl) initScratch initArgs initSource]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro finished reachable
  have done := commit_leaf_loop_finished initialized 0 8 (by decide) finished reachable
  have finalLink : finished.getReg .x1 = 4312 := by
    rw [done.1]
    simpa [initialized, MachineState.getReg_setPC, MachineState.getReg_setReg_ne] using link
  have finalPC : finished.pc = 4776 := by
    rw [done.2 (by decide)]
    simp [initialized, MachineState.setPC]
  rw [commit_leaf_return finished finalPC finalLink]
  simp [instructionCycles, Execution.charge, ← Nat.add_assoc]

private theorem commit_leaf_block_preserves (state : MachineState) (answer : BitVec 256) (reg : Reg)
    (preserved : reg ∉ [.x6, .x8]) :
    (commitLeafStepState state answer).getReg reg = state.getReg reg := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at preserved
  rcases preserved with ⟨not6, not8⟩
  simp only [commitLeafStepState, commitLeafAdvanceState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not8)]
  exact (commit_compression_register _ answer reg).trans
    (commit_copy_register state 8 (by decide) reg not6)

/-- The complete hash preserves the position/path metadata, proof pointer, root
pointer, and scratch pointer. It consumes exactly 32 bytes per block from x8. -/
theorem commit_leaf_loop_registers (state : MachineState) (count : Nat) (finished : MachineState)
    (reachable : finished ∈ support (commitLeafLoop state count)) :
    finished.getReg .x8 = state.getReg .x8 + BitVec.ofNat 64 (32 * count) ∧
    ∀ reg ∉ [.x6, .x8], finished.getReg reg = state.getReg reg := by
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
