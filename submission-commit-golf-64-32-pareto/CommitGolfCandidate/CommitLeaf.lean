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

private def commitCompressionInstructions : List Instr :=
  [.ADDI .x5 .x0 0, .ADDI .x10 .x21 0, .ADDI .x11 .x0 64,
   .ADDI .x12 .x21 0, .ADDI .x13 .x0 0]

private def commitCompressionPrefix (state : MachineState) (count : Nat) : MachineState :=
  (commitCompressionInstructions.take count).foldl execInstrBr state

/-- State after the compression reply overwrites the low half of scratch memory. -/
def commitCompressionState (state : MachineState) (answer : BitVec 256) : MachineState :=
  writeBits (commitCompressionPrefix state 5) 256 answer

/-- Install the eight-block counter and the fixed compression ABI once. -/
private def commitLeafPrepareInstructions : List Instr :=
  [.ADDI .x28 .x0 8, .ADDI .x5 .x0 0, .ADDI .x10 .x21 0, .ADDI .x11 .x0 64,
   .ADDI .x12 .x21 0, .ADDI .x13 .x0 0]

private def commitLeafPreparePrefix (state : MachineState) (count : Nat) : MachineState :=
  (commitLeafPrepareInstructions.take count).foldl execInstrBr state

/-- Loop entry after the one-time setup. Scratch is the compression source and destination. -/
def commitLeafPrepared (state : MachineState) : MachineState :=
  ((((((state.setReg .x28 8).setReg .x5 0).setReg .x10 (state.getReg .x21)).setReg .x11 64).setReg
    .x12 (state.getReg .x21)).setReg .x13 0).setPC 4456

theorem commitLeafPrepared_register (state : MachineState) (reg : Reg)
    (not28 : reg ≠ .x28) (not5 : reg ≠ .x5) (not10 : reg ≠ .x10)
    (not11 : reg ≠ .x11) (not12 : reg ≠ .x12) (not13 : reg ≠ .x13) :
    (commitLeafPrepared state).getReg reg = state.getReg reg := by
  simp only [commitLeafPrepared, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not13),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not12),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not11),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not10),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not5),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not28)]

theorem commit_leaf_prepare (state : MachineState) (pc : state.pc = 4432)
    (scratch : state.getReg .x21 = 256) (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (6 + fuel) state allowCoins =
      (do let result ← execute (submission.image .commit) fuel (commitLeafPrepared state) allowCoins
          return result.charge 6 0) := by
  have steps (remaining : Nat) :
      execute (submission.image .commit) (6 + remaining) state allowCoins =
        (do let result ← execute (submission.image .commit) remaining
              (commitLeafPreparePrefix state 6) allowCoins
            return result.charge 6 0) := by
    apply execute_unit_steps (states := commitLeafPreparePrefix state)
    intro i hi
    refine ⟨.base ((commitLeafPrepareInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · apply commit_fetch _ (84 + i) _ (by omega)
      · interval_cases i <;>
          simp [commitLeafPreparePrefix, commitLeafPrepareInstructions, execInstrBr, pc, MachineState.setPC]
      · interval_cases i <;> rfl
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl
  have same : commitLeafPreparePrefix state 6 = commitLeafPrepared state := by
    simp [commitLeafPreparePrefix, commitLeafPrepareInstructions, commitLeafPrepared, execInstrBr,
      signExtend12, scratch, MachineState.getReg, MachineState.setReg, MachineState.setPC, pc]
  rw [steps, same]

/-- Reply written by one bare compression syscall. Registers are unchanged. -/
def commitLeafEcallState (state : MachineState) (answer : BitVec 256) : MachineState :=
  writeBits state 256 answer

/-- The block syscall assumes the ABI already installed by `commit_leaf_prepare`. -/
theorem commit_leaf_ecall (state : MachineState) (pc : state.pc = 4488)
    (selector : state.getReg .x5 = 0) (source : state.getReg .x10 = 256)
    (length : state.getReg .x11 = 64) (destination : state.getReg .x12 = 256)
    (kind : state.getReg .x13 = 0) (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (1 + fuel) state allowCoins =
      (do let answer ← World.query (.inr (.inl (readBuffer state 256 64)))
          let result ← execute (submission.image .commit) fuel
            (commitLeafEcallState state answer) allowCoins
          return result.charge 8 1) := by
  have fetched : fetch (submission.image .commit) state = some (.base .ECALL) := by
    apply commit_fetch _ 98 _ (by decide) pc; rfl
  have input : oracleInput state = some (.inl (readBuffer state 256 64)) := by
    have h13 : (state.getReg .x13).toNat = 0 := by rw [kind]; rfl
    have h11 : (state.getReg .x11).toNat = 64 := by rw [length]; rfl
    unfold oracleInput
    rw [h13, h11, source, destination]
    simp [COMPRESSION_INPUT_LENGTH, COMPRESSION_OUTPUT_LENGTH, rangeValid, MEMORY_BYTES,
      BitVec.ofNat_toNat, BitVec.toNat_ofNat]
  rw [Nat.add_comm 1 fuel, execute, fetched, if_pos selector, input]
  simp [writeOracleAnswer, destination, commitLeafEcallState, oracleCycles,
    COMPRESSION_CYCLES, Execution.charge]
  rfl

theorem commit_leaf_ecall_register (state : MachineState) (answer : BitVec 256) (reg : Reg) :
    (commitLeafEcallState state answer).getReg reg = state.getReg reg := by
  rw [commitLeafEcallState, writeBits_register]

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

set_option maxHeartbeats 800000 in
/-- Copy the next 256-bit message block into the upper scratch half. -/
theorem commit_leaf_copy (state : MachineState) (pc : state.pc = 4456)
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
  · apply commit_fetch _ (90 + i) _ (by omega)
    · interval_cases i <;>
        simp [commitLeafCopyPrefix, commitLeafCopyInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
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

/-- The leaf-loop latch advances to the next block, then decrements the eight-block counter. -/
def commitLeafNextState (state : MachineState) : MachineState :=
  ((state.setReg .x8 (state.getReg .x8 + 32)).setReg .x28 (state.getReg .x28 - 1)).setPC
    (if state.getReg .x28 - 1 = 0 then 4504 else 4456)

theorem commit_leaf_next (state : MachineState) (pc : state.pc = 4492)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (3 + fuel) state allowCoins =
      (do let result ← execute (submission.image .commit) fuel (commitLeafNextState state) allowCoins
          return result.charge 3 0) := by
  let advanced := (state.setReg .x8 (state.getReg .x8 + 32)).setPC 4496
  let next := (advanced.setReg .x28 (state.getReg .x28 - 1)).setPC 4500
  have f0 : fetch (submission.image .commit) state = some (.base (.ADDI .x8 .x8 32)) := by
    apply commit_fetch _ 99 _ (by decide) pc; rfl
  have f1 : fetch (submission.image .commit) advanced = some (.base (.ADDI .x28 .x28 4095)) := by
    apply commit_fetch _ 100 _ (by decide) rfl; rfl
  have f2 : fetch (submission.image .commit) next = some (.base (.BNE .x28 .x0 8148)) := by
    apply commit_fetch _ 101 _ (by decide) rfl; rfl
  have s0 : ordinaryStep state (.base (.ADDI .x8 .x8 32)) = some advanced := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, pc, advanced]
  have s1 : ordinaryStep advanced (.base (.ADDI .x28 .x28 4095)) = some next := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, advanced, next,
      MachineState.getReg, MachineState.setReg, MachineState.setPC, BitVec.sub_eq_add_neg]
  have s2 : ordinaryStep next (.base (.BNE .x28 .x0 8148)) = some (commitLeafNextState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13,
      advanced, next, commitLeafNextState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    split <;> simp_all
  rw [Nat.add_comm 3 fuel]
  simp only [execute, f0, s0, f1, s1, f2, s2, instructionCycles, bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

/-- One leaf block: copy 32 bytes, compress, then advance the pointer and counter. -/
def commitLeafStepState (state : MachineState) (answer : BitVec 256) : MachineState :=
  commitLeafNextState (commitLeafEcallState (commitLeafCopyState state) answer)

theorem commit_leaf_block (state : MachineState) (pc : state.pc = 4456)
    (scratch : state.getReg .x21 = 256)
    (selector : state.getReg .x5 = 0) (source : state.getReg .x10 = 256)
    (length : state.getReg .x11 = 64) (destination : state.getReg .x12 = 256)
    (kind : state.getReg .x13 = 0)
    (sourceValid : ∀ word : Fin 4,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (12 + fuel) state allowCoins =
      (do let answer ← World.query (.inr (.inl (readBuffer (commitLeafCopyState state) 256 64)))
          let result ← execute (submission.image .commit) fuel (commitLeafStepState state answer) allowCoins
          return result.charge 19 1) := by
  have copyPC : (commitLeafCopyState state).pc = 4488 := by
    simp [commitLeafCopyState, commitLeafCopyPrefix, commitLeafCopyInstructions, execInstrBr,
      MachineState.setPC, pc]
  have copyReg (reg : Reg) (not6 : reg ≠ .x6) :
      (commitLeafCopyState state).getReg reg = state.getReg reg :=
    commit_copy_register state 8 (by decide) reg not6
  have ecallPC (answer : BitVec 256) :
      (commitLeafEcallState (commitLeafCopyState state) answer).pc = 4492 := by
    simp [commitLeafEcallState, writeBits, MachineState.setPC, copyPC]
  rw [show 12 + fuel = 8 + (1 + (3 + fuel)) by omega, commit_leaf_copy state pc scratch sourceValid,
    commit_leaf_ecall _ copyPC (copyReg .x5 (by decide) |>.trans selector)
      (copyReg .x10 (by decide) |>.trans source) (copyReg .x11 (by decide) |>.trans length)
      (copyReg .x12 (by decide) |>.trans destination) (copyReg .x13 (by decide) |>.trans kind)]
  simp only [bind_assoc, pure_bind]
  apply congrArg (fun continuation =>
    (liftM (World.query (.inr (.inl (readBuffer (commitLeafCopyState state) 256 64)))) :
      OracleComp World (BitVec 256)) >>= continuation)
  funext answer
  rw [commit_leaf_next _ (ecallPC answer)]
  simp [commitLeafStepState, Execution.charge, ← Nat.add_assoc]

/-- The next iteration has the advanced source pointer and decremented counter;
its scratch pointer and subroutine return address are unchanged. -/
theorem commit_leaf_block_registers (state : MachineState) (answer : BitVec 256) :
    (commitLeafStepState state answer).getReg .x8 = state.getReg .x8 + 32 ∧
    (commitLeafStepState state answer).getReg .x28 = state.getReg .x28 - 1 ∧
    (commitLeafStepState state answer).getReg .x21 = state.getReg .x21 ∧
    (commitLeafStepState state answer).getReg .x1 = state.getReg .x1 := by
  have preserved (reg : Reg) (not6 : reg ≠ .x6) (not5 : reg ≠ .x5) (not10 : reg ≠ .x10)
      (not11 : reg ≠ .x11) (not12 : reg ≠ .x12) (not13 : reg ≠ .x13) :
      (commitLeafEcallState (commitLeafCopyState state) answer).getReg reg = state.getReg reg :=
    (commit_leaf_ecall_register _ answer reg).trans
      (commit_copy_register state 8 (by decide) reg not6)
  simp only [commitLeafStepState, commitLeafNextState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_eq (by decide : Reg.x8 ≠ .x0),
    MachineState.getReg_setReg_eq (by decide : Reg.x28 ≠ .x0),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x28 ≠ .x8),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x28 ≠ .x21),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x8 ≠ .x21),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x28 ≠ .x1),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x8 ≠ .x1)]
  rw [preserved .x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    preserved .x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    preserved .x21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    preserved .x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem commit_leaf_block_pc (state : MachineState) (answer : BitVec 256) :
    (commitLeafStepState state answer).pc =
      if state.getReg .x28 - 1 = 0 then 4504 else 4456 := by
  change (if (commitLeafEcallState (commitLeafCopyState state) answer).getReg .x28 - 1 = 0
    then 4504 else 4456) = _
  rw [commit_leaf_ecall_register, commitLeafCopyState, commit_copy_register state 8 (by decide) .x28 (by decide)]

/-- A semantic unfolding of the actual block loop. Each iteration issues the exact
scratch query from the image and applies its byte-writing and pointer transitions. -/
def commitLeafLoop (state : MachineState) : Nat → OracleComp World MachineState
  | 0 => pure state
  | count + 1 => do
      let answer ← World.query (.inr (.inl (readBuffer (commitLeafCopyState state) 256 64)))
      commitLeafLoop (commitLeafStepState state answer) count

/-- Exact execution of the leaf hash loop for every possible sequence of oracle replies.
The loop uses 12 instructions and 19 cycles per block, and makes one query per block. -/
theorem commit_leaf_loop (state : MachineState) (count : Nat) (bounded : count ≤ 8)
    (pc : 0 < count → state.pc = 4456) (counter : state.getReg .x28 = BitVec.ofNat 64 count)
    (scratch : state.getReg .x21 = 256)
    (selector : state.getReg .x5 = 0) (source : state.getReg .x10 = 256)
    (length : state.getReg .x11 = 64) (destination : state.getReg .x12 = 256)
    (kind : state.getReg .x13 = 0)
    (sourceValid : ∀ word < 4 * count,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (12 * count + fuel) state allowCoins =
      (do let finished ← commitLeafLoop state count
          let result ← execute (submission.image .commit) fuel finished allowCoins
          return result.charge (19 * count) count) := by
  induction count generalizing state with
  | zero => simp [commitLeafLoop, Execution.charge]
  | succ count ih =>
    have currentValid (word : Fin 4) :
        accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word.val)) 8 = true :=
      sourceValid word.val (by omega)
    have nextCounter (answer : BitVec 256) :
        (commitLeafStepState state answer).getReg .x28 = BitVec.ofNat 64 count := by
      rw [(commit_leaf_block_registers state answer).2.1, counter]
      change BitVec.ofNat 64 (count + 1) - BitVec.ofNat 64 1 = BitVec.ofNat 64 count
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (count + 1) 1 (by decide) (by omega)]
      congr 1
    have nextPC (answer : BitVec 256) (positive : 0 < count) :
        (commitLeafStepState state answer).pc = 4456 := by
      rw [commit_leaf_block_pc]
      have nonzero : state.getReg .x28 - 1 ≠ 0 := by
        rw [← (commit_leaf_block_registers state answer).2.1, nextCounter]
        intro zero
        have := congrArg BitVec.toNat zero
        change count % 18446744073709551616 = 0 at this
        omega
      exact if_neg nonzero
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
    have keep (reg : Reg) (not6 : reg ≠ .x6) (not8 : reg ≠ .x8) (not28 : reg ≠ .x28)
        (answer : BitVec 256) : (commitLeafStepState state answer).getReg reg = state.getReg reg := by
      simp only [commitLeafStepState, commitLeafNextState, MachineState.getReg_setPC,
        MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not28),
        MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not8)]
      exact (commit_leaf_ecall_register _ answer reg).trans
        (commit_copy_register state 8 (by decide) reg not6)
    rw [show 12 * (count + 1) + fuel = 12 + (12 * count + fuel) by omega,
      commit_leaf_block state (pc (by omega)) scratch selector source length destination kind currentValid]
    simp only [commitLeafLoop, bind_assoc]
    apply congrArg (fun continuation =>
      (liftM (World.query (.inr (.inl (readBuffer (commitLeafCopyState state) 256 64)))) :
        OracleComp World (BitVec 256)) >>= continuation)
    funext answer
    rw [ih _ (by omega) (nextPC answer) (nextCounter answer)
      ((commit_leaf_block_registers state answer).2.2.1.trans scratch)
      (keep .x5 (by decide) (by decide) (by decide) answer |>.trans selector)
      (keep .x10 (by decide) (by decide) (by decide) answer |>.trans source)
      (keep .x11 (by decide) (by decide) (by decide) answer |>.trans length)
      (keep .x12 (by decide) (by decide) (by decide) answer |>.trans destination)
      (keep .x13 (by decide) (by decide) (by decide) answer |>.trans kind) (nextValid answer)]
    simp [Execution.charge, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- Every possible run of the bounded loop exhausts its counter and preserves the
return address. A nonempty loop reaches the actual JALR instruction. -/
theorem commit_leaf_loop_finished (state : MachineState) (count : Nat) (bounded : count ≤ 8)
    (counter : state.getReg .x28 = BitVec.ofNat 64 count) (finished : MachineState)
    (reachable : finished ∈ support (commitLeafLoop state count)) :
    finished.getReg .x28 = 0 ∧ finished.getReg .x1 = state.getReg .x1 ∧
      (0 < count → finished.pc = 4504) := by
  induction count generalizing state with
  | zero =>
    simp only [commitLeafLoop, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    exact ⟨counter, rfl, by omega⟩
  | succ count ih =>
    simp only [commitLeafLoop, mem_support_bind_iff] at reachable
    obtain ⟨answer, _, reached⟩ := reachable
    have nextCounter : (commitLeafStepState state answer).getReg .x28 = BitVec.ofNat 64 count := by
      rw [(commit_leaf_block_registers state answer).2.1, counter]
      change BitVec.ofNat 64 (count + 1) - BitVec.ofNat 64 1 = BitVec.ofNat 64 count
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (count + 1) 1 (by decide) (by omega)]
      congr 1
    have remaining := ih _ (by omega) nextCounter reached
    refine ⟨remaining.1, remaining.2.1.trans (commit_leaf_block_registers state answer).2.2.2, ?_⟩
    intro _
    by_cases empty : count = 0
    · subst count
      simp only [commitLeafLoop, support_pure, Set.mem_singleton_iff] at reached
      subst finished
      rw [commit_leaf_block_pc state answer, counter]
      rfl
    · exact remaining.2.2 (by omega)

/-- The leaf subroutine returns to its caller using the preserved link register. -/
theorem commit_leaf_return (state : MachineState) (pc : state.pc = 4504)
    (link : state.getReg .x1 = 4292) (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (1 + fuel) state allowCoins =
      (do let result ← execute (submission.image .commit) fuel (state.setPC 4292) allowCoins
          return result.charge 1 0) := by
  have fetched : fetch (submission.image .commit) state =
      some (.base (.JALR .x0 .x1 0)) := by
    apply commit_fetch _ 102 _ (by decide) pc
    rfl
  have stepped : ordinaryStep state (.base (.JALR .x0 .x1 0)) = some (state.setPC 4292) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      MachineState.setReg, link]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

/-- The full 2048-bit leaf-hashing subroutine: install the compression ABI once,
process eight blocks, and return to the leaf-digest store. All oracle replies are covered.
It takes 103 instructions, costs exactly 159 cycles, and makes eight queries. -/
theorem commit_leaf_subroutine (state : MachineState) (pc : state.pc = 4432)
    (link : state.getReg .x1 = 4292) (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word < 32,
      accessValid (state.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .commit) (103 + fuel) state allowCoins =
      (do let finished ← commitLeafLoop (commitLeafPrepared state) 8
          let result ← execute (submission.image .commit) fuel (finished.setPC 4292) allowCoins
          return result.charge 159 8) := by
  let initialized := commitLeafPrepared state
  have initCounter : initialized.getReg .x28 = BitVec.ofNat 64 8 := by
    simp [initialized, commitLeafPrepared, MachineState.getReg, MachineState.setReg, MachineState.setPC]
  have initScratch : initialized.getReg .x21 = 256 := by
    simpa [initialized, commitLeafPrepared, MachineState.getReg_setPC, MachineState.getReg_setReg_ne] using scratch
  have initSource : ∀ word < 4 * 8,
      accessValid (initialized.getReg .x8 + BitVec.ofNat 64 (8 * word)) 8 = true := by
    simpa [initialized, commitLeafPrepared, MachineState.getReg_setPC, MachineState.getReg_setReg_ne] using sourceValid
  have initAbi : initialized.getReg .x5 = 0 ∧ initialized.getReg .x10 = 256 ∧
      initialized.getReg .x11 = 64 ∧ initialized.getReg .x12 = 256 ∧ initialized.getReg .x13 = 0 := by
    simp [initialized, commitLeafPrepared, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    simpa [MachineState.getReg] using scratch
  rw [show 103 + fuel = 6 + (12 * 8 + (1 + fuel)) by omega, commit_leaf_prepare state pc scratch,
    commit_leaf_loop initialized 8 (by decide) (fun _ => rfl) initCounter initScratch
      initAbi.1 initAbi.2.1 initAbi.2.2.1 initAbi.2.2.2.1 initAbi.2.2.2.2 initSource]
  simp only [bind_assoc, pure_bind]
  apply bind_congr_of_forall_mem_support
  intro finished reachable
  have done := commit_leaf_loop_finished initialized 8 (by decide) initCounter finished reachable
  have finalLink : finished.getReg .x1 = 4292 := by
    rw [done.2.1]
    simpa [initialized, commitLeafPrepared, MachineState.getReg_setPC, MachineState.getReg_setReg_ne] using link
  rw [commit_leaf_return finished (done.2.2 (by decide)) finalLink]
  simp [instructionCycles, Execution.charge, ← Nat.add_assoc]

private theorem commit_leaf_block_preserves (state : MachineState) (answer : BitVec 256) (reg : Reg)
    (preserved : reg ∉ [.x5, .x6, .x8, .x10, .x11, .x12, .x13, .x28]) :
    (commitLeafStepState state answer).getReg reg = state.getReg reg := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at preserved
  rcases preserved with ⟨not5, not6, not8, not10, not11, not12, not13, not28⟩
  simp only [commitLeafStepState, commitLeafNextState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not28),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not8)]
  exact (commit_leaf_ecall_register _ answer reg).trans
    (commit_copy_register state 8 (by decide) reg not6)

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
