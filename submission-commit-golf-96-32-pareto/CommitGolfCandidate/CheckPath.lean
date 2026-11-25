import CommitGolfCandidate.Check

/-! Execution of the checker's authentication path. The low bit of the position
selects sibling ordering. Both branches use the same compression primitive. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

private def pathCopySource (start : Nat) : Reg := if start = 31 then .x21 else .x25
private def pathCopyOffset (start : Nat) : Nat := if start = 39 ∨ start = 15 then 0 else 32

private def pathCopyInstructions (start : Nat) : List Instr :=
  [.LD .x6 (pathCopySource start) 0, .SD .x21 .x6 (BitVec.ofNat 12 (pathCopyOffset start)),
   .LD .x6 (pathCopySource start) 8, .SD .x21 .x6 (BitVec.ofNat 12 (pathCopyOffset start + 8)),
   .LD .x6 (pathCopySource start) 16, .SD .x21 .x6 (BitVec.ofNat 12 (pathCopyOffset start + 16)),
   .LD .x6 (pathCopySource start) 24, .SD .x21 .x6 (BitVec.ofNat 12 (pathCopyOffset start + 24))]

private def pathCopyPrefix (state : MachineState) (start count : Nat) : MachineState :=
  ((pathCopyInstructions start).take count).foldl execInstrBr state

def checkPathCopyState (state : MachineState) (start : Nat) : MachineState :=
  pathCopyPrefix state start 8

private theorem path_copy_register (state : MachineState) (start count : Nat)
    (bounded : count ≤ 8) (reg : Reg) (notScratch : reg ≠ .x6) :
    (pathCopyPrefix state start count).getReg reg = state.getReg reg := by
  have memRegister (state : MachineState) (address value : Word) (reg : Reg) :
      (state.setMem address value).getReg reg = state.getReg reg := by cases reg <;> rfl
  interval_cases count <;>
    simp only [pathCopyPrefix, pathCopyInstructions, List.take, List.foldl, execInstrBr,
      MachineState.getReg_setPC, memRegister,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm notScratch)]

theorem check_path_copy_register (state : MachineState) (start : Nat) (reg : Reg)
    (notScratch : reg ≠ .x6) :
    (checkPathCopyState state start).getReg reg = state.getReg reg :=
  path_copy_register state start 8 (by decide) reg notScratch

theorem check_path_copy_pc (state : MachineState) (start : Nat) :
    (checkPathCopyState state start).pc = state.pc + 32 := by
  simp [checkPathCopyState, pathCopyPrefix, pathCopyInstructions, execInstrBr,
    MachineState.setPC, BitVec.add_assoc]

set_option maxHeartbeats 1000000 in
/-- Each copy in the two ordering branches uses eight ordinary instructions.
The path locations and the identical salt-copy block are checked against the actual encoded image. -/
theorem check_path_copy (state : MachineState) (start : Nat)
    (location : start = 31 ∨ start = 39 ∨ start = 48 ∨ start = 15)
    (pc : state.pc = BitVec.ofNat 64 (4096 + 4 * start))
    (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word : Fin 4,
      accessValid (state.getReg (pathCopySource start) + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (8 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel (checkPathCopyState state start) allowCoins
          return result.charge 8 0) := by
  apply execute_unit_steps (states := pathCopyPrefix state start)
  intro i hi
  refine ⟨.base (((pathCopyInstructions start)[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply check_fetch _ (start + i) _ (by rcases location with rfl | rfl | rfl | rfl <;> omega)
    · rcases location with rfl | rfl | rfl | rfl <;> interval_cases i <;>
        simp [pathCopyPrefix, pathCopyInstructions, execInstrBr, pc, MachineState.setPC]
    · rcases location with rfl | rfl | rfl | rfl <;> interval_cases i <;> rfl
  · have sourceReg := path_copy_register state start i (by omega) (pathCopySource start)
      (by rcases location with rfl | rfl | rfl | rfl <;> decide)
    have scratchReg := (path_copy_register state start i (by omega) .x21 (by decide)).trans scratch
    have s0 := sourceValid ⟨0, by decide⟩
    have s1 := sourceValid ⟨1, by decide⟩
    have s2 := sourceValid ⟨2, by decide⟩
    have s3 := sourceValid ⟨3, by decide⟩
    have valid : memoryArgumentsValid (pathCopyPrefix state start i)
        (((pathCopyInstructions start)[i]?).getD .EBREAK) = true := by
      interval_cases i <;>
        simp only [pathCopyInstructions, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.getD_some, memoryArgumentsValid, memAccess, sourceReg, scratchReg, signExtend12] <;>
        first | exact s0 | exact s1 | exact s2 | exact s3 |
          (rcases location with rfl | rfl | rfl | rfl <;> rfl)
    interval_cases i <;>
      simp only [pathCopyInstructions, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep, valid, ↓reduceIte] <;> rfl
  · interval_cases i <;> rfl

/-- After ANDI and BEQ, even positions put the sibling on the right; odd positions
first move the current digest to the right and then copy the sibling on the left. -/
def checkPathBranchState (state : MachineState) : MachineState :=
  (state.setReg .x7 (state.getReg .x20 &&& 1)).setPC
    (if state.getReg .x20 &&& 1 = 0 then 4288 else 4220)

theorem check_path_branch (state : MachineState) (pc : state.pc = 4212)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (2 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel (checkPathBranchState state) allowCoins
          return result.charge 2 0) := by
  let next := (state.setReg .x7 (state.getReg .x20 &&& 1)).setPC 4216
  have f0 : fetch (submission.image .check) state = some (.base (.ANDI .x7 .x20 1)) := by
    apply check_fetch _ 29 _ (by decide) pc; rfl
  have f1 : fetch (submission.image .check) next = some (.base (.BEQ .x7 .x0 72)) := by
    apply check_fetch _ 30 _ (by decide) rfl; rfl
  have s0 : ordinaryStep state (.base (.ANDI .x7 .x20 1)) = some next := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, next, pc]
  have s1 : ordinaryStep next (.base (.BEQ .x7 .x0 72)) = some (checkPathBranchState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13,
      next, checkPathBranchState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    split <;> simp_all
  rw [Nat.add_comm 2 fuel]
  simp only [execute, f0, s0, f1, s1, instructionCycles, bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

private theorem path_jump (state : MachineState) (pc : state.pc = 4284)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (1 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel (state.setPC 4320) allowCoins
          return result.charge 1 0) := by
  have fetched : fetch (submission.image .check) state = some (.base (.JAL .x0 36)) := by
    apply check_fetch _ 47 _ (by decide) pc; rfl
  have stepped : ordinaryStep state (.base (.JAL .x0 36)) = some (state.setPC 4320) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend21,
      MachineState.setReg, pc]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

/-- Scratch prepared in the order selected by the position's low bit. -/
def checkPathPreparedState (state : MachineState) : MachineState :=
  if state.getReg .x20 &&& 1 = 0 then
    checkPathCopyState (checkPathBranchState state) 48
  else
    (checkPathCopyState (checkPathCopyState (checkPathBranchState state) 31) 39).setPC 4320

/-- Preparation costs ten instructions on the left branch and nineteen on the right. -/
def pathPreparationSteps (index : Word) : Nat := if index &&& 1 = 0 then 10 else 19

private theorem path_branch_register (state : MachineState) (reg : Reg) (notScratch : reg ≠ .x7) :
    (checkPathBranchState state).getReg reg = state.getReg reg := by
  simp only [checkPathBranchState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm notScratch)]

/-- Both sibling-ordering branches arrive at the shared compression block. -/
theorem check_path_preparation (state : MachineState) (pc : state.pc = 4212)
    (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word : Fin 4,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (pathPreparationSteps (state.getReg .x20) + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel (checkPathPreparedState state) allowCoins
          return result.charge (pathPreparationSteps (state.getReg .x20)) 0) := by
  let branched := checkPathBranchState state
  have scratchB : branched.getReg .x21 = 256 :=
    (path_branch_register state .x21 (by decide)).trans scratch
  have sourceB (word : Fin 4) :
      accessValid (branched.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
    rw [path_branch_register state .x25 (by decide)]
    exact sourceValid word
  by_cases even : state.getReg .x20 &&& 1 = 0
  · have branchPC : branched.pc = 4288 := if_pos even
    have source : ∀ word : Fin 4,
        accessValid (branched.getReg (pathCopySource 48) + BitVec.ofNat 64 (8 * word.val)) 8 = true :=
      sourceB
    simp only [pathPreparationSteps, even, if_true, checkPathPreparedState]
    rw [show 10 + fuel = 2 + (8 + fuel) by omega, check_path_branch state pc,
      check_path_copy branched 48 (Or.inr (Or.inr (Or.inl rfl))) branchPC scratchB source]
    simp [Execution.charge, branched, ← Nat.add_assoc]
  · have branchPC : branched.pc = 4220 := if_neg even
    have source : ∀ word : Fin 4,
        accessValid (branched.getReg (pathCopySource 31) + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
      intro ⟨word, bounded⟩
      change accessValid (branched.getReg .x21 + BitVec.ofNat 64 (8 * word)) 8 = true
      rw [scratchB]
      interval_cases word <;> rfl
    let moved := checkPathCopyState branched 31
    have movedPC : moved.pc = 4252 := by rw [check_path_copy_pc, branchPC]; rfl
    have movedScratch : moved.getReg .x21 = 256 :=
      (check_path_copy_register branched 31 .x21 (by decide)).trans scratchB
    have movedSource (word : Fin 4) :
        accessValid (moved.getReg (pathCopySource 39) + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
      change accessValid (moved.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true
      rw [check_path_copy_register branched 31 .x25 (by decide)]
      exact sourceB word
    have jumpPC : (checkPathCopyState moved 39).pc = 4284 := by
      rw [check_path_copy_pc, movedPC]; rfl
    simp only [pathPreparationSteps, even, if_false, checkPathPreparedState]
    rw [show 19 + fuel = 2 + (8 + (8 + (1 + fuel))) by omega, check_path_branch state pc,
      check_path_copy branched 31 (Or.inl rfl) branchPC scratchB source,
      check_path_copy moved 39 (Or.inr (Or.inl rfl)) movedPC movedScratch movedSource,
      path_jump _ jumpPC]
    simp [Execution.charge, branched, moved, ← Nat.add_assoc]

theorem check_path_prepared_pc (state : MachineState) :
    (checkPathPreparedState state).pc = 4320 := by
  unfold checkPathPreparedState
  split
  · rw [check_path_copy_pc]
    change (if state.getReg .x20 &&& 1 = 0 then 4288 else 4220) + 32 = 4320
    simp_all
  · rfl

theorem check_path_prepared_register (state : MachineState) (reg : Reg)
    (not6 : reg ≠ .x6) (not7 : reg ≠ .x7) :
    (checkPathPreparedState state).getReg reg = state.getReg reg := by
  unfold checkPathPreparedState
  split <;> simp only [MachineState.getReg_setPC,
    check_path_copy_register _ _ reg not6, path_branch_register state reg not7]

/-- After one hash, consume the sibling, shift the position, and decrement the depth. -/
def checkPathNextState (state : MachineState) : MachineState :=
  (((state.setReg .x25 (state.getReg .x25 + 32)).setReg .x20 (state.getReg .x20 >>> 1)).setReg
    .x29 (state.getReg .x29 - 1)).setPC (if state.getReg .x29 - 1 = 0 then 4360 else 4212)

theorem check_path_next (state : MachineState) (pc : state.pc = 4344)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (4 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel (checkPathNextState state) allowCoins
          return result.charge 4 0) := by
  let advanced := (state.setReg .x25 (state.getReg .x25 + 32)).setPC 4348
  let shifted := (advanced.setReg .x20 (state.getReg .x20 >>> 1)).setPC 4352
  let next := (shifted.setReg .x29 (state.getReg .x29 - 1)).setPC 4356
  have f0 : fetch (submission.image .check) state = some (.base (.ADDI .x25 .x25 32)) := by
    apply check_fetch _ 62 _ (by decide) pc; rfl
  have f1 : fetch (submission.image .check) advanced = some (.base (.SRLI .x20 .x20 1)) := by
    apply check_fetch _ 63 _ (by decide) rfl; rfl
  have f2 : fetch (submission.image .check) shifted = some (.base (.ADDI .x29 .x29 4095)) := by
    apply check_fetch _ 64 _ (by decide) rfl; rfl
  have f3 : fetch (submission.image .check) next = some (.base (.BNE .x29 .x0 8048)) := by
    apply check_fetch _ 65 _ (by decide) rfl; rfl
  have s0 : ordinaryStep state (.base (.ADDI .x25 .x25 32)) = some advanced := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, advanced, pc]
  have s1 : ordinaryStep advanced (.base (.SRLI .x20 .x20 1)) = some shifted := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, advanced, shifted,
      MachineState.getReg, MachineState.setReg, MachineState.setPC]
  have s2 : ordinaryStep shifted (.base (.ADDI .x29 .x29 4095)) = some next := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, advanced, shifted, next,
      MachineState.getReg, MachineState.setReg, MachineState.setPC, BitVec.sub_eq_add_neg]
  have s3 : ordinaryStep next (.base (.BNE .x29 .x0 8048)) = some (checkPathNextState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13,
      advanced, shifted, next, checkPathNextState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    split <;> simp_all
  rw [Nat.add_comm 4 fuel]
  simp only [execute, f0, s0, f1, s1, f2, s2, f3, s3, instructionCycles, bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

/-- One path level, including sibling ordering, compression, and the loop latch. -/
def checkPathStepState (state : MachineState) (answer : BitVec 256) : MachineState :=
  checkPathNextState (checkCompressionState (checkPathPreparedState state) answer)

theorem check_path_step (state : MachineState) (pc : state.pc = 4212)
    (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word : Fin 4,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (pathPreparationSteps (state.getReg .x20) + 26 + fuel) state allowCoins =
      (do let answer ← World.query (.inr (.inl (padInput (readBuffer (checkPathPreparedState state) 256 64))))
          let result ← execute (submission.image .check) fuel (checkPathStepState state answer) allowCoins
          return result.charge (pathPreparationSteps (state.getReg .x20) + 33) 1) := by
  have preparedPC := check_path_prepared_pc state
  have preparedScratch : (checkPathPreparedState state).getReg .x21 = 256 :=
    (check_path_prepared_register state .x21 (by decide) (by decide)).trans scratch
  have compressionPC (answer : BitVec 256) :
      (checkCompressionState (checkPathPreparedState state) answer).pc = 4344 := by
    rw [check_compression_pc, preparedPC]
    rfl
  rw [show pathPreparationSteps (state.getReg .x20) + 26 + fuel =
      pathPreparationSteps (state.getReg .x20) + (22 + (4 + fuel)) by omega,
    check_path_preparation state pc scratch sourceValid,
    check_compression _ 56 rfl preparedPC preparedScratch]
  simp only [bind_assoc, pure_bind]
  apply congrArg (fun continuation =>
    (liftM (World.query (.inr (.inl (padInput (readBuffer (checkPathPreparedState state) 256 64))))) :
      OracleComp World (BitVec 256)) >>= continuation)
  funext answer
  rw [check_path_next _ (compressionPC answer)]
  simp [checkPathStepState, Execution.charge, ← Nat.add_assoc]

private theorem path_compression_register (state : MachineState) (answer : BitVec 256) (reg : Reg)
    (not5 : reg ≠ .x5) (not6 : reg ≠ .x6) (not7 : reg ≠ .x7) (not10 : reg ≠ .x10)
    (not11 : reg ≠ .x11) (not12 : reg ≠ .x12) (not13 : reg ≠ .x13)
    (not14 : reg ≠ .x14 := by decide) (not15 : reg ≠ .x15 := by decide)
    (not16 : reg ≠ .x16 := by decide) (not17 : reg ≠ .x17 := by decide)
    (not31 : reg ≠ .x31 := by decide) :
    (checkCompressionState (checkPathPreparedState state) answer).getReg reg = state.getReg reg :=
  (check_compression_register _ answer reg not5 not10 not11 not12 not13 not14 not15 not16 not17 not31).trans
    (check_path_prepared_register state reg not6 not7)

/-- The path loop consumes one sibling, shifts the index, and reduces its depth.
No oracle reply can change these control registers. -/
theorem check_path_step_registers (state : MachineState) (answer : BitVec 256) :
    (checkPathStepState state answer).getReg .x25 = state.getReg .x25 + 32 ∧
    (checkPathStepState state answer).getReg .x20 = state.getReg .x20 >>> 1 ∧
    (checkPathStepState state answer).getReg .x29 = state.getReg .x29 - 1 ∧
    (checkPathStepState state answer).getReg .x21 = state.getReg .x21 := by
  simp only [checkPathStepState, checkPathNextState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_eq (by decide : Reg.x25 ≠ .x0),
    MachineState.getReg_setReg_eq (by decide : Reg.x20 ≠ .x0),
    MachineState.getReg_setReg_eq (by decide : Reg.x29 ≠ .x0),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x29 ≠ .x25),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x20 ≠ .x25),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x29 ≠ .x20),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x29 ≠ .x21),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x20 ≠ .x21),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x25 ≠ .x21)]
  rw [path_compression_register state answer .x25 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide),
    path_compression_register state answer .x20 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide),
    path_compression_register state answer .x29 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide),
    path_compression_register state answer .x21 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem check_path_step_pc (state : MachineState) (answer : BitVec 256) :
    (checkPathStepState state answer).pc = if state.getReg .x29 - 1 = 0 then 4360 else 4212 := by
  change (if (checkCompressionState (checkPathPreparedState state) answer).getReg .x29 - 1 = 0
    then 4360 else 4212) = _
  rw [path_compression_register state answer .x29 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)]

/-- Instruction count follows the public position's bits, independently of replies. -/
def pathInstructions (index : Word) : Nat → Nat
  | 0 => 0
  | count + 1 => pathPreparationSteps index + 26 + pathInstructions (index >>> 1) count

/-- Exactly one oracle query for each level, using the actual prepared scratch input. -/
def checkPathLoop (state : MachineState) : Nat → OracleComp World MachineState
  | 0 => pure state
  | count + 1 => do
      let answer ← World.query (.inr (.inl (padInput (readBuffer (checkPathPreparedState state) 256 64))))
      checkPathLoop (checkPathStepState state answer) count

/-- Each left level uses 36 instructions; each right level uses 45.
Seven extra cycles per level account for the eight-cycle compression syscall. -/
theorem path_instruction_bounds (index : Word) (count : Nat) :
    36 * count ≤ pathInstructions index count ∧ pathInstructions index count ≤ 45 * count := by
  induction count generalizing index with
  | zero => simp [pathInstructions]
  | succ count ih =>
    have tail := ih (index >>> 1)
    simp only [pathInstructions, pathPreparationSteps]
    split <;> omega

/-- Exact execution of the whole authentication-path loop, with branch-dependent
fuel and cycles. Every possible sequence of oracle replies is covered. -/
theorem check_path_loop (state : MachineState) (count : Nat) (bounded : count ≤ 24)
    (pc : 0 < count → state.pc = 4212) (counter : state.getReg .x29 = BitVec.ofNat 64 count)
    (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word < 4 * count,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (pathInstructions (state.getReg .x20) count + fuel) state allowCoins =
      (do let finished ← checkPathLoop state count
          let result ← execute (submission.image .check) fuel finished allowCoins
          return result.charge (pathInstructions (state.getReg .x20) count + 7 * count) count) := by
  induction count generalizing state with
  | zero => simp [pathInstructions, checkPathLoop, Execution.charge]
  | succ count ih =>
    have currentValid (word : Fin 4) :
        accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true :=
      sourceValid word.val (by omega)
    have nextCounter (answer : BitVec 256) :
        (checkPathStepState state answer).getReg .x29 = BitVec.ofNat 64 count := by
      rw [(check_path_step_registers state answer).2.2.1, counter]
      change BitVec.ofNat 64 (count + 1) - BitVec.ofNat 64 1 = BitVec.ofNat 64 count
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (count + 1) 1 (by decide) (by omega)]
      congr 1
    have nextPC (answer : BitVec 256) (positive : 0 < count) :
        (checkPathStepState state answer).pc = 4212 := by
      rw [check_path_step_pc state answer]
      have nonzero : state.getReg .x29 - 1 ≠ 0 := by
        rw [← (check_path_step_registers state answer).2.2.1, nextCounter]
        intro zero
        have numeric := congrArg BitVec.toNat zero
        change count % 18446744073709551616 = 0 at numeric
        omega
      exact if_neg nonzero
    have nextValid (answer : BitVec 256) (word : Nat) (bound : word < 4 * count) :
        accessValid ((checkPathStepState state answer).getReg .x25 +
          BitVec.ofNat 64 (8 * word)) 8 = true := by
      have valid := sourceValid (word + 4) (by omega)
      rw [(check_path_step_registers state answer).1]
      have address : state.getReg .x25 + 32 + BitVec.ofNat 64 (8 * word) =
          state.getReg .x25 + BitVec.ofNat 64 (8 * (word + 4)) := by
        rw [show 8 * (word + 4) = 32 + 8 * word by omega, BitVec.ofNat_add, BitVec.add_assoc]
        rfl
      rw [address]
      exact valid
    rw [pathInstructions, Nat.add_assoc, check_path_step state (pc (by omega)) scratch currentValid]
    simp only [checkPathLoop, bind_assoc]
    apply congrArg (fun continuation =>
      (liftM (World.query (.inr (.inl (padInput (readBuffer (checkPathPreparedState state) 256 64))))) :
        OracleComp World (BitVec 256)) >>= continuation)
    funext answer
    rw [← (check_path_step_registers state answer).2.1,
      ih _ (by omega) (nextPC answer) (nextCounter answer)
        ((check_path_step_registers state answer).2.2.2.trans scratch) (nextValid answer)]
    simp only [(check_path_step_registers state answer).2.1, bind_assoc, pure_bind]
    have charges (result : Execution) :
        (result.charge (pathInstructions (state.getReg .x20 >>> 1) count + 7 * count) count).charge
          (pathPreparationSteps (state.getReg .x20) + 33) 1 =
        result.charge (pathPreparationSteps (state.getReg .x20) + 26 +
          pathInstructions (state.getReg .x20 >>> 1) count + 7 * (count + 1)) (count + 1) := by
      cases result
      simp only [Execution.charge, Execution.mk.injEq, true_and]
      constructor <;> omega
    simp only [charges]

/-- Every completed nonempty path reaches the root-comparison block with zero depth. -/
theorem check_path_loop_finished (state : MachineState) (count : Nat) (bounded : count ≤ 24)
    (counter : state.getReg .x29 = BitVec.ofNat 64 count) (finished : MachineState)
    (reachable : finished ∈ support (checkPathLoop state count)) :
    finished.getReg .x29 = 0 ∧ (0 < count → finished.pc = 4360) := by
  induction count generalizing state with
  | zero =>
    simp only [checkPathLoop, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    exact ⟨counter, by omega⟩
  | succ count ih =>
    simp only [checkPathLoop, mem_support_bind_iff] at reachable
    obtain ⟨answer, _, reached⟩ := reachable
    have nextCounter : (checkPathStepState state answer).getReg .x29 = BitVec.ofNat 64 count := by
      rw [(check_path_step_registers state answer).2.2.1, counter]
      change BitVec.ofNat 64 (count + 1) - BitVec.ofNat 64 1 = BitVec.ofNat 64 count
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (count + 1) 1 (by decide) (by omega)]
      congr 1
    have rest := ih _ (by omega) nextCounter reached
    refine ⟨rest.1, ?_⟩
    intro _
    by_cases empty : count = 0
    · subst count
      simp only [checkPathLoop, support_pure, Set.mem_singleton_iff] at reached
      subst finished
      rw [check_path_step_pc state answer, counter]
      rfl
    · exact rest.2 (by omega)

private theorem path_step_preserves (state : MachineState) (answer : BitVec 256) (reg : Reg)
    (preserved : reg ∉ [.x5, .x6, .x7, .x10, .x11, .x12, .x13, .x20, .x25, .x29, .x14, .x15, .x16, .x17, .x31]) :
    (checkPathStepState state answer).getReg reg = state.getReg reg := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at preserved
  rcases preserved with ⟨not5, not6, not7, not10, not11, not12, not13, not20, not25, not29, not14, not15, not16, not17, not31⟩
  simp only [checkPathStepState, checkPathNextState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not29),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not20),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not25)]
  exact path_compression_register state answer reg not5 not6 not7 not10 not11 not12 not13 not14 not15 not16 not17 not31

/-- Across the loop, exactly 32 bytes per sibling are consumed. The outer position
counter, index-list pointer, supplied-root pointer, and scratch pointer survive. -/
theorem check_path_loop_registers (state : MachineState) (count : Nat) (finished : MachineState)
    (reachable : finished ∈ support (checkPathLoop state count)) :
    finished.getReg .x25 = state.getReg .x25 + BitVec.ofNat 64 (32 * count) ∧
    ∀ reg ∉ [.x5, .x6, .x7, .x10, .x11, .x12, .x13, .x20, .x25, .x29, .x14, .x15, .x16, .x17, .x31],
      finished.getReg reg = state.getReg reg := by
  induction count generalizing state with
  | zero =>
    simp only [checkPathLoop, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    simp
  | succ count ih =>
    simp only [checkPathLoop, mem_support_bind_iff] at reachable
    obtain ⟨answer, _, reached⟩ := reachable
    have rest := ih _ reached
    constructor
    · rw [rest.1, (check_path_step_registers state answer).1]
      rw [show 32 * (count + 1) = 32 + 32 * count by omega, BitVec.ofNat_add, BitVec.add_assoc]
      rfl
    · intro reg preserved
      exact (rest.2 reg preserved).trans (path_step_preserves state answer reg preserved)

/-- The 24-level loop uses 24 queries and at most 1248 cycles (1032 for all-left).
This bound includes all copies, branches, compression syscalls, and loop latches. -/
theorem check_path_cycle_bounds (index : Word) :
    1032 ≤ pathInstructions index 24 + 7 * 24 ∧ pathInstructions index 24 + 7 * 24 ≤ 1248 := by
  have bounds := path_instruction_bounds index 24
  omega

private def pathSetupInstructions : List Instr :=
  [.ADDI .x29 .x0 0, .SLLI .x29 .x29 11, .ADDI .x29 .x29 24, .BEQ .x29 .x0 152]

private def pathSetupPrefix (state : MachineState) (count : Nat) : MachineState :=
  (pathSetupInstructions.take count).foldl execInstrBr state

def checkPathInitializedState (state : MachineState) : MachineState := pathSetupPrefix state 4

theorem check_path_initialized_counter (state : MachineState) :
    (checkPathInitializedState state).getReg .x29 = BitVec.ofNat 64 24 := by
  dsimp only [checkPathInitializedState, pathSetupPrefix, pathSetupInstructions, List.take, List.foldl,
    execInstrBr, signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC]
  simp

/-- Four instructions initialize the path depth after the leaf-hash return. -/
theorem check_path_setup (state : MachineState) (pc : state.pc = 4196)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (4 + fuel) state allowCoins =
      (do let result ← execute (submission.image .check) fuel (checkPathInitializedState state) allowCoins
          return result.charge 4 0) := by
  apply execute_unit_steps (states := pathSetupPrefix state)
  intro i hi
  refine ⟨.base ((pathSetupInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply check_fetch _ (25 + i) _ (by omega)
    · interval_cases i <;>
        simp [pathSetupPrefix, pathSetupInstructions, execInstrBr, pc, MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

theorem check_path_setup_register (state : MachineState) (reg : Reg) (notCounter : reg ≠ .x29) :
    (checkPathInitializedState state).getReg reg = state.getReg reg := by
  cases reg <;> simp_all [checkPathInitializedState, pathSetupPrefix, pathSetupInstructions,
    execInstrBr, signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC]

/-- Complete execution from the leaf-hash return to the root-comparison block.
The caller supplies readable words for all 24 siblings; no hash-output assumption
is required. The additional four cycles initialize the fixed path depth. -/
theorem check_path_subroutine (state : MachineState) (pc : state.pc = 4196)
    (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word < 96,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute (submission.image .check) (4 + pathInstructions (state.getReg .x20) 24 + fuel) state allowCoins =
      (do let finished ← checkPathLoop (checkPathInitializedState state) 24
          let result ← execute (submission.image .check) fuel finished allowCoins
          return result.charge (4 + pathInstructions (state.getReg .x20) 24 + 168) 24) := by
  have initialPC : (checkPathInitializedState state).pc = 4212 := by
    simp [checkPathInitializedState, pathSetupPrefix, pathSetupInstructions, execInstrBr,
      signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC, pc]
  have counter : (checkPathInitializedState state).getReg .x29 = BitVec.ofNat 64 24 := by
    dsimp only [checkPathInitializedState, pathSetupPrefix, pathSetupInstructions, List.take, List.foldl,
      execInstrBr, signExtend12, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    simp
  have initialScratch := (check_path_setup_register state .x21 (by decide)).trans scratch
  have initialSource : ∀ word < 4 * 24,
      accessValid ((checkPathInitializedState state).getReg .x25 + BitVec.ofNat 64 (8 * word)) 8 = true := by
    rw [check_path_setup_register state .x25 (by decide)]
    exact sourceValid
  rw [Nat.add_assoc, check_path_setup state pc,
    ← check_path_setup_register state .x20 (by decide),
    check_path_loop _ 24 (by decide) (fun _ => initialPC) counter initialScratch initialSource]
  simp only [bind_assoc, pure_bind, check_path_setup_register state .x20 (by decide)]
  simp [Execution.charge, Nat.add_assoc]

end CommitGolfCandidate
