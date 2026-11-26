import CommitGolfCandidate.PairControl
import CommitGolfCandidate.PairLeaf
namespace CommitGolfCandidate.PairCap

open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

set_option maxRecDepth 12000

set_option maxHeartbeats 1400000

def rec_pathCopySource (start : Nat) : Reg := if start = 29 then .x21 else .x25

def rec_pathCopyOffset (start : Nat) : Nat := if start = 37 ∨ start = 16 then 0 else 32

def rec_pathCopyInstructions (start : Nat) : List Instr :=
  [.LD .x6 (rec_pathCopySource start) 0, .SD .x21 .x6 (BitVec.ofNat 12 (rec_pathCopyOffset start)),
   .LD .x6 (rec_pathCopySource start) 8, .SD .x21 .x6 (BitVec.ofNat 12 (rec_pathCopyOffset start + 8)),
   .LD .x6 (rec_pathCopySource start) 16, .SD .x21 .x6 (BitVec.ofNat 12 (rec_pathCopyOffset start + 16)),
   .LD .x6 (rec_pathCopySource start) 24, .SD .x21 .x6 (BitVec.ofNat 12 (rec_pathCopyOffset start + 24))]

def rec_pathCopyPrefix (state : MachineState) (start count : Nat) : MachineState :=
  ((rec_pathCopyInstructions start).take count).foldl execInstrBr state

theorem rec_path_copy_register (state : MachineState) (start count : Nat)
    (bounded : count ≤ 8) (reg : Reg) (notScratch : reg ≠ .x6) :
    (rec_pathCopyPrefix state start count).getReg reg = state.getReg reg := by
  have memRegister (state : MachineState) (address value : Word) (reg : Reg) :
      (state.setMem address value).getReg reg = state.getReg reg := by cases reg <;> rfl
  interval_cases count <;>
    simp only [rec_pathCopyPrefix, rec_pathCopyInstructions, List.take, List.foldl, execInstrBr,
      MachineState.getReg_setPC, memRegister,
      MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm notScratch)]

theorem rec_check_path_copy (state : MachineState) (start : Nat)
    (location : start = 29 ∨ start = 37 ∨ start = 46 )
    (pc : state.pc = BitVec.ofNat 64 (4864 + 4 * start))
    (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word : Fin 4,
      accessValid (state.getReg (rec_pathCopySource start) + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute Late.Check.Normal.checkerImage (8 + fuel) state allowCoins =
      (do let result ← execute Late.Check.Normal.checkerImage fuel (Late.Check.Normal.checkPathCopyState state start) allowCoins
          return result.charge 8 0) := by
  apply execute_unit_steps (states := rec_pathCopyPrefix state start)
  intro i hi
  refine ⟨.base (((rec_pathCopyInstructions start)[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply patchedFetch _ (192 + start + i) _ (by rcases location with rfl | rfl | rfl <;> omega)
    · rcases location with rfl | rfl | rfl <;> interval_cases i <;>
        simp [rec_pathCopyPrefix, rec_pathCopyInstructions, execInstrBr, pc, MachineState.setPC]
    · rcases location with rfl | rfl | rfl <;> interval_cases i <;> rfl
  · have sourceReg := rec_path_copy_register state start i (by omega) (rec_pathCopySource start)
      (by rcases location with rfl | rfl | rfl <;> decide)
    have scratchReg := (rec_path_copy_register state start i (by omega) .x21 (by decide)).trans scratch
    have s0 := sourceValid ⟨0, by decide⟩
    have s1 := sourceValid ⟨1, by decide⟩
    have s2 := sourceValid ⟨2, by decide⟩
    have s3 := sourceValid ⟨3, by decide⟩
    have valid : memoryArgumentsValid (rec_pathCopyPrefix state start i)
        (((rec_pathCopyInstructions start)[i]?).getD .EBREAK) = true := by
      interval_cases i <;>
        simp only [rec_pathCopyInstructions, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Option.getD_some, memoryArgumentsValid, memAccess, sourceReg, scratchReg, signExtend12] <;>
        first | exact s0 | exact s1 | exact s2 | exact s3 |
          (rcases location with rfl | rfl | rfl <;> rfl)
    interval_cases i <;>
      simp only [rec_pathCopyInstructions, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.getD_some] at valid ⊢ <;>
      simp only [ordinaryStep, valid, ↓reduceIte] <;> rfl
  · interval_cases i <;> rfl

def rec_checkPathBranchState (state : MachineState) : MachineState :=
  (state.setReg .x7 (state.getReg .x20 &&& 1)).setPC
    (if state.getReg .x20 &&& 1 = 0 then 5048 else 4980)

theorem rec_check_path_branch (state : MachineState) (pc : state.pc = 4972)
    (fuel : Nat) (allowCoins : Bool) :
    execute Late.Check.Normal.checkerImage (2 + fuel) state allowCoins =
      (do let result ← execute Late.Check.Normal.checkerImage fuel (rec_checkPathBranchState state) allowCoins
          return result.charge 2 0) := by
  let next := (state.setReg .x7 (state.getReg .x20 &&& 1)).setPC 4976
  have f0 : fetch Late.Check.Normal.checkerImage state = some (.base (.ANDI .x7 .x20 1)) := by
    apply patchedFetch _ 219 _ (by decide) pc; rfl
  have f1 : fetch Late.Check.Normal.checkerImage next = some (.base (.BEQ .x7 .x0 72)) := by
    apply patchedFetch _ 220 _ (by decide) rfl; rfl
  have s0 : ordinaryStep state (.base (.ANDI .x7 .x20 1)) = some next := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, next, pc]
  have s1 : ordinaryStep next (.base (.BEQ .x7 .x0 72)) = some (rec_checkPathBranchState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13,
      next, rec_checkPathBranchState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    split <;> simp_all
  rw [Nat.add_comm 2 fuel]
  simp only [execute, f0, s0, f1, s1, instructionCycles, bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

theorem rec_path_jump (state : MachineState) (pc : state.pc = 5044)
    (fuel : Nat) (allowCoins : Bool) :
    execute Late.Check.Normal.checkerImage (1 + fuel) state allowCoins =
      (do let result ← execute Late.Check.Normal.checkerImage fuel (state.setPC 5080) allowCoins
          return result.charge 1 0) := by
  have fetched : fetch Late.Check.Normal.checkerImage state = some (.base (.JAL .x0 36)) := by
    apply patchedFetch _ 237 _ (by decide) pc; rfl
  have stepped : ordinaryStep state (.base (.JAL .x0 36)) = some (state.setPC 5080) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend21,
      MachineState.setReg, pc]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

def rec_checkPathPreparedState (state : MachineState) : MachineState :=
  if state.getReg .x20 &&& 1 = 0 then
    Late.Check.Normal.checkPathCopyState (rec_checkPathBranchState state) 46
  else
    (Late.Check.Normal.checkPathCopyState (Late.Check.Normal.checkPathCopyState (rec_checkPathBranchState state) 29) 37).setPC 5080

theorem rec_path_branch_register (state : MachineState) (reg : Reg) (notScratch : reg ≠ .x7) :
    (rec_checkPathBranchState state).getReg reg = state.getReg reg := by
  simp only [rec_checkPathBranchState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm notScratch)]

theorem rec_check_path_preparation (state : MachineState) (pc : state.pc = 4972)
    (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word : Fin 4,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute Late.Check.Normal.checkerImage (Late.Check.Normal.pathPreparationSteps (state.getReg .x20) + fuel) state allowCoins =
      (do let result ← execute Late.Check.Normal.checkerImage fuel (rec_checkPathPreparedState state) allowCoins
          return result.charge (Late.Check.Normal.pathPreparationSteps (state.getReg .x20)) 0) := by
  let branched := rec_checkPathBranchState state
  have scratchB : branched.getReg .x21 = 256 :=
    (rec_path_branch_register state .x21 (by decide)).trans scratch
  have sourceB (word : Fin 4) :
      accessValid (branched.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
    rw [rec_path_branch_register state .x25 (by decide)]
    exact sourceValid word
  by_cases even : state.getReg .x20 &&& 1 = 0
  · have branchPC : branched.pc = 5048 := if_pos even
    have source : ∀ word : Fin 4,
        accessValid (branched.getReg (rec_pathCopySource 46) + BitVec.ofNat 64 (8 * word.val)) 8 = true :=
      sourceB
    simp only [Late.Check.Normal.pathPreparationSteps, even, if_true, rec_checkPathPreparedState]
    rw [show 10 + fuel = 2 + (8 + fuel) by omega, rec_check_path_branch state pc,
      rec_check_path_copy branched 46 (Or.inr (Or.inr rfl)) branchPC scratchB source]
    simp [Execution.charge, branched, ← Nat.add_assoc]
  · have branchPC : branched.pc = 4980 := if_neg even
    have source : ∀ word : Fin 4,
        accessValid (branched.getReg (rec_pathCopySource 29) + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
      intro ⟨word, bounded⟩
      change accessValid (branched.getReg .x21 + BitVec.ofNat 64 (8 * word)) 8 = true
      rw [scratchB]
      interval_cases word <;> rfl
    let moved := Late.Check.Normal.checkPathCopyState branched 29
    have movedPC : moved.pc = 5012 := by rw [Late.Check.Normal.check_path_copy_pc, branchPC]; rfl
    have movedScratch : moved.getReg .x21 = 256 :=
      (Late.Check.Normal.check_path_copy_register branched 29 .x21 (by decide)).trans scratchB
    have movedSource (word : Fin 4) :
        accessValid (moved.getReg (rec_pathCopySource 37) + BitVec.ofNat 64 (8 * word.val)) 8 = true := by
      change accessValid (moved.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true
      rw [Late.Check.Normal.check_path_copy_register branched 29 .x25 (by decide)]
      exact sourceB word
    have jumpPC : (Late.Check.Normal.checkPathCopyState moved 37).pc = 5044 := by
      rw [Late.Check.Normal.check_path_copy_pc, movedPC]; rfl
    simp only [Late.Check.Normal.pathPreparationSteps, even, if_false, rec_checkPathPreparedState]
    rw [show 19 + fuel = 2 + (8 + (8 + (1 + fuel))) by omega, rec_check_path_branch state pc,
      rec_check_path_copy branched 29 (Or.inl rfl) branchPC scratchB source,
      rec_check_path_copy moved 37 (Or.inr (Or.inl rfl)) movedPC movedScratch movedSource,
      rec_path_jump _ jumpPC]
    simp [Execution.charge, branched, moved, ← Nat.add_assoc]

theorem rec_check_path_prepared_pc (state : MachineState) :
    (rec_checkPathPreparedState state).pc = 5080 := by
  unfold rec_checkPathPreparedState
  split
  · rw [Late.Check.Normal.check_path_copy_pc]
    change (if state.getReg .x20 &&& 1 = 0 then 5048 else 4980) + 32 = 5080
    simp_all
  · rfl

theorem rec_check_path_prepared_register (state : MachineState) (reg : Reg)
    (not6 : reg ≠ .x6) (not7 : reg ≠ .x7) :
    (rec_checkPathPreparedState state).getReg reg = state.getReg reg := by
  unfold rec_checkPathPreparedState
  split <;> simp only [MachineState.getReg_setPC,
    Late.Check.Normal.check_path_copy_register _ _ reg not6, rec_path_branch_register state reg not7]

def rec_checkPathNextState (state : MachineState) : MachineState :=
  (((state.setReg .x25 (state.getReg .x25 + 32)).setReg .x20 (state.getReg .x20 >>> 1)).setReg
    .x29 (state.getReg .x29 - 1)).setPC (if state.getReg .x29 - 1 = 0 then 5120 else 4972)

theorem rec_check_path_next (state : MachineState) (pc : state.pc = 5104)
    (fuel : Nat) (allowCoins : Bool) :
    execute Late.Check.Normal.checkerImage (4 + fuel) state allowCoins =
      (do let result ← execute Late.Check.Normal.checkerImage fuel (rec_checkPathNextState state) allowCoins
          return result.charge 4 0) := by
  let advanced := (state.setReg .x25 (state.getReg .x25 + 32)).setPC 5108
  let shifted := (advanced.setReg .x20 (state.getReg .x20 >>> 1)).setPC 5112
  let next := (shifted.setReg .x29 (state.getReg .x29 - 1)).setPC 5116
  have f0 : fetch Late.Check.Normal.checkerImage state = some (.base (.ADDI .x25 .x25 32)) := by
    apply patchedFetch _ 252 _ (by decide) pc; rfl
  have f1 : fetch Late.Check.Normal.checkerImage advanced = some (.base (.SRLI .x20 .x20 1)) := by
    apply patchedFetch _ 253 _ (by decide) rfl; rfl
  have f2 : fetch Late.Check.Normal.checkerImage shifted = some (.base (.ADDI .x29 .x29 4095)) := by
    apply patchedFetch _ 254 _ (by decide) rfl; rfl
  have f3 : fetch Late.Check.Normal.checkerImage next = some (.base (.BNE .x29 .x0 8048)) := by
    apply patchedFetch _ 255 _ (by decide) rfl; rfl
  have s0 : ordinaryStep state (.base (.ADDI .x25 .x25 32)) = some advanced := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, advanced, pc]
  have s1 : ordinaryStep advanced (.base (.SRLI .x20 .x20 1)) = some shifted := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, advanced, shifted,
      MachineState.getReg, MachineState.setReg, MachineState.setPC]
  have s2 : ordinaryStep shifted (.base (.ADDI .x29 .x29 4095)) = some next := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12, advanced, shifted, next,
      MachineState.getReg, MachineState.setReg, MachineState.setPC, BitVec.sub_eq_add_neg]
  have s3 : ordinaryStep next (.base (.BNE .x29 .x0 8048)) = some (rec_checkPathNextState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13,
      advanced, shifted, next, rec_checkPathNextState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    split <;> simp_all
  rw [Nat.add_comm 4 fuel]
  simp only [execute, f0, s0, f1, s1, f2, s2, f3, s3, instructionCycles, bind_assoc, pure_bind]
  simp [Execution.charge, ← Nat.add_assoc]

def rec_checkPathStepState (state : MachineState) (answer : BitVec 256) : MachineState :=
  rec_checkPathNextState (Late.Check.Normal.checkCompressionState (rec_checkPathPreparedState state) answer)

theorem rec_check_path_step (state : MachineState) (pc : state.pc = 4972)
    (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word : Fin 4,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute Late.Check.Normal.checkerImage (Late.Check.Normal.pathPreparationSteps (state.getReg .x20) + 26 + fuel) state allowCoins =
      (do let answer ← World.query (.inr (.inl (padInput (readBuffer (rec_checkPathPreparedState state) 256 64))))
          let result ← execute Late.Check.Normal.checkerImage fuel (rec_checkPathStepState state answer) allowCoins
          return result.charge (Late.Check.Normal.pathPreparationSteps (state.getReg .x20) + 33) 1) := by
  have preparedPC := rec_check_path_prepared_pc state
  have preparedScratch : (rec_checkPathPreparedState state).getReg .x21 = 256 :=
    (rec_check_path_prepared_register state .x21 (by decide) (by decide)).trans scratch
  have compressionPC (answer : BitVec 256) :
      (Late.Check.Normal.checkCompressionState (rec_checkPathPreparedState state) answer).pc = 5104 := by
    rw [Late.Check.Normal.check_compression_pc, preparedPC]
    rfl
  rw [show Late.Check.Normal.pathPreparationSteps (state.getReg .x20) + 26 + fuel =
      Late.Check.Normal.pathPreparationSteps (state.getReg .x20) + (22 + (4 + fuel)) by omega,
    rec_check_path_preparation state pc scratch sourceValid,
    rec_check_compression _ 54 rfl preparedPC preparedScratch]
  simp only [bind_assoc, pure_bind]
  apply congrArg (fun continuation =>
    (liftM (World.query (.inr (.inl (padInput (readBuffer (rec_checkPathPreparedState state) 256 64))))) :
      OracleComp World (BitVec 256)) >>= continuation)
  funext answer
  rw [rec_check_path_next _ (compressionPC answer)]
  simp [rec_checkPathStepState, Execution.charge, ← Nat.add_assoc]

theorem rec_path_compression_register (state : MachineState) (answer : BitVec 256) (reg : Reg)
    (not5 : reg ≠ .x5) (not6 : reg ≠ .x6) (not7 : reg ≠ .x7) (not10 : reg ≠ .x10)
    (not11 : reg ≠ .x11) (not12 : reg ≠ .x12) (not13 : reg ≠ .x13)
    (not14 : reg ≠ .x14 := by decide) (not15 : reg ≠ .x15 := by decide)
    (not16 : reg ≠ .x16 := by decide) (not17 : reg ≠ .x17 := by decide)
    (not31 : reg ≠ .x31 := by decide) :
    (Late.Check.Normal.checkCompressionState (rec_checkPathPreparedState state) answer).getReg reg = state.getReg reg :=
  (Late.Check.Normal.check_compression_register _ answer reg not5 not10 not11 not12 not13 not14 not15 not16 not17 not31).trans
    (rec_check_path_prepared_register state reg not6 not7)

theorem rec_check_path_step_registers (state : MachineState) (answer : BitVec 256) :
    (rec_checkPathStepState state answer).getReg .x25 = state.getReg .x25 + 32 ∧
    (rec_checkPathStepState state answer).getReg .x20 = state.getReg .x20 >>> 1 ∧
    (rec_checkPathStepState state answer).getReg .x29 = state.getReg .x29 - 1 ∧
    (rec_checkPathStepState state answer).getReg .x21 = state.getReg .x21 := by
  simp only [rec_checkPathStepState, rec_checkPathNextState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_eq (by decide : Reg.x25 ≠ .x0),
    MachineState.getReg_setReg_eq (by decide : Reg.x20 ≠ .x0),
    MachineState.getReg_setReg_eq (by decide : Reg.x29 ≠ .x0),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x29 ≠ .x25),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x20 ≠ .x25),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x29 ≠ .x20),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x29 ≠ .x21),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x20 ≠ .x21),
    MachineState.getReg_setReg_ne _ _ _ _ (by decide : Reg.x25 ≠ .x21)]
  rw [rec_path_compression_register state answer .x25 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide),
    rec_path_compression_register state answer .x20 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide),
    rec_path_compression_register state answer .x29 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide),
    rec_path_compression_register state answer .x21 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem rec_check_path_step_pc (state : MachineState) (answer : BitVec 256) :
    (rec_checkPathStepState state answer).pc = if state.getReg .x29 - 1 = 0 then 5120 else 4972 := by
  change (if (Late.Check.Normal.checkCompressionState (rec_checkPathPreparedState state) answer).getReg .x29 - 1 = 0
    then 5120 else 4972) = _
  rw [rec_path_compression_register state answer .x29 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)]

def rec_checkPathLoop (state : MachineState) : Nat → OracleComp World MachineState
  | 0 => pure state
  | count + 1 => do
      let answer ← World.query (.inr (.inl (padInput (readBuffer (rec_checkPathPreparedState state) 256 64))))
      rec_checkPathLoop (rec_checkPathStepState state answer) count

theorem rec_check_path_loop (state : MachineState) (count : Nat) (bounded : count ≤ 24)
    (pc : 0 < count → state.pc = 4972) (counter : state.getReg .x29 = BitVec.ofNat 64 count)
    (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word < 4 * count,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute Late.Check.Normal.checkerImage (Late.Check.Normal.pathInstructions (state.getReg .x20) count + fuel) state allowCoins =
      (do let finished ← rec_checkPathLoop state count
          let result ← execute Late.Check.Normal.checkerImage fuel finished allowCoins
          return result.charge (Late.Check.Normal.pathInstructions (state.getReg .x20) count + 7 * count) count) := by
  induction count generalizing state with
  | zero => simp [Late.Check.Normal.pathInstructions, rec_checkPathLoop, Execution.charge]
  | succ count ih =>
    have currentValid (word : Fin 4) :
        accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word.val)) 8 = true :=
      sourceValid word.val (by omega)
    have nextCounter (answer : BitVec 256) :
        (rec_checkPathStepState state answer).getReg .x29 = BitVec.ofNat 64 count := by
      rw [(rec_check_path_step_registers state answer).2.2.1, counter]
      change BitVec.ofNat 64 (count + 1) - BitVec.ofNat 64 1 = BitVec.ofNat 64 count
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (count + 1) 1 (by decide) (by omega)]
      congr 1
    have nextPC (answer : BitVec 256) (positive : 0 < count) :
        (rec_checkPathStepState state answer).pc = 4972 := by
      rw [rec_check_path_step_pc state answer]
      have nonzero : state.getReg .x29 - 1 ≠ 0 := by
        rw [← (rec_check_path_step_registers state answer).2.2.1, nextCounter]
        intro zero
        have numeric := congrArg BitVec.toNat zero
        change count % 18446744073709551616 = 0 at numeric
        omega
      exact if_neg nonzero
    have nextValid (answer : BitVec 256) (word : Nat) (bound : word < 4 * count) :
        accessValid ((rec_checkPathStepState state answer).getReg .x25 +
          BitVec.ofNat 64 (8 * word)) 8 = true := by
      have valid := sourceValid (word + 4) (by omega)
      rw [(rec_check_path_step_registers state answer).1]
      have address : state.getReg .x25 + 32 + BitVec.ofNat 64 (8 * word) =
          state.getReg .x25 + BitVec.ofNat 64 (8 * (word + 4)) := by
        rw [show 8 * (word + 4) = 32 + 8 * word by omega, BitVec.ofNat_add, BitVec.add_assoc]
        rfl
      rw [address]
      exact valid
    rw [Late.Check.Normal.pathInstructions, Nat.add_assoc, rec_check_path_step state (pc (by omega)) scratch currentValid]
    simp only [rec_checkPathLoop, bind_assoc]
    apply congrArg (fun continuation =>
      (liftM (World.query (.inr (.inl (padInput (readBuffer (rec_checkPathPreparedState state) 256 64))))) :
        OracleComp World (BitVec 256)) >>= continuation)
    funext answer
    rw [← (rec_check_path_step_registers state answer).2.1,
      ih _ (by omega) (nextPC answer) (nextCounter answer)
        ((rec_check_path_step_registers state answer).2.2.2.trans scratch) (nextValid answer)]
    simp only [(rec_check_path_step_registers state answer).2.1, bind_assoc, pure_bind]
    have charges (result : Execution) :
        (result.charge (Late.Check.Normal.pathInstructions (state.getReg .x20 >>> 1) count + 7 * count) count).charge
          (Late.Check.Normal.pathPreparationSteps (state.getReg .x20) + 33) 1 =
        result.charge (Late.Check.Normal.pathPreparationSteps (state.getReg .x20) + 26 +
          Late.Check.Normal.pathInstructions (state.getReg .x20 >>> 1) count + 7 * (count + 1)) (count + 1) := by
      cases result
      simp only [Execution.charge, Execution.mk.injEq, true_and]
      constructor <;> omega
    simp only [charges]

theorem rec_check_path_loop_finished (state : MachineState) (count : Nat) (bounded : count ≤ 24)
    (counter : state.getReg .x29 = BitVec.ofNat 64 count) (finished : MachineState)
    (reachable : finished ∈ support (rec_checkPathLoop state count)) :
    finished.getReg .x29 = 0 ∧ (0 < count → finished.pc = 5120) := by
  induction count generalizing state with
  | zero =>
    simp only [rec_checkPathLoop, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    exact ⟨counter, by omega⟩
  | succ count ih =>
    simp only [rec_checkPathLoop, mem_support_bind_iff] at reachable
    obtain ⟨answer, _, reached⟩ := reachable
    have nextCounter : (rec_checkPathStepState state answer).getReg .x29 = BitVec.ofNat 64 count := by
      rw [(rec_check_path_step_registers state answer).2.2.1, counter]
      change BitVec.ofNat 64 (count + 1) - BitVec.ofNat 64 1 = BitVec.ofNat 64 count
      rw [BitVec.ofNat_sub_ofNat_of_le (w := 64) (count + 1) 1 (by decide) (by omega)]
      congr 1
    have rest := ih _ (by omega) nextCounter reached
    refine ⟨rest.1, ?_⟩
    intro _
    by_cases empty : count = 0
    · subst count
      simp only [rec_checkPathLoop, support_pure, Set.mem_singleton_iff] at reached
      subst finished
      rw [rec_check_path_step_pc state answer, counter]
      rfl
    · exact rest.2 (by omega)

theorem rec_path_step_preserves (state : MachineState) (answer : BitVec 256) (reg : Reg)
    (preserved : reg ∉ [.x5, .x6, .x7, .x10, .x11, .x12, .x13, .x20, .x25, .x29, .x14, .x15, .x16, .x17, .x31]) :
    (rec_checkPathStepState state answer).getReg reg = state.getReg reg := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at preserved
  rcases preserved with ⟨not5, not6, not7, not10, not11, not12, not13, not20, not25, not29, not14, not15, not16, not17, not31⟩
  simp only [rec_checkPathStepState, rec_checkPathNextState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not29),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not20),
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm not25)]
  exact rec_path_compression_register state answer reg not5 not6 not7 not10 not11 not12 not13 not14 not15 not16 not17 not31

theorem rec_check_path_loop_registers (state : MachineState) (count : Nat) (finished : MachineState)
    (reachable : finished ∈ support (rec_checkPathLoop state count)) :
    finished.getReg .x25 = state.getReg .x25 + BitVec.ofNat 64 (32 * count) ∧
    finished.getReg .x20 = state.getReg .x20 >>> count ∧
    ∀ reg ∉ [.x5, .x6, .x7, .x10, .x11, .x12, .x13, .x20, .x25, .x29, .x14, .x15, .x16, .x17, .x31],
      finished.getReg reg = state.getReg reg := by
  induction count generalizing state with
  | zero =>
    simp only [rec_checkPathLoop, support_pure, Set.mem_singleton_iff] at reachable
    subst finished
    simp
  | succ count ih =>
    simp only [rec_checkPathLoop, mem_support_bind_iff] at reachable
    obtain ⟨answer, _, reached⟩ := reachable
    have rest := ih _ reached
    refine ⟨?_, ?_, ?_⟩
    · rw [rest.1, (rec_check_path_step_registers state answer).1]
      rw [show 32 * (count + 1) = 32 + 32 * count by omega, BitVec.ofNat_add, BitVec.add_assoc]
      rfl
    · rw [rest.2.1, (rec_check_path_step_registers state answer).2.1]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul]
      congr 1
      simp [Nat.pow_succ, Nat.mul_comm]
    · intro reg preserved
      exact (rest.2.2 reg preserved).trans (rec_path_step_preserves state answer reg preserved)

def rec_checkPathInitializedState (state : MachineState) : MachineState :=
  (state.setReg .x29 (state.getReg .x30)).setPC 4972

theorem rec_check_path_initialized_counter (state : MachineState) :
    (rec_checkPathInitializedState state).getReg .x29 = state.getReg .x30 := rfl

theorem rec_check_path_setup (state : MachineState) (pc : state.pc = 4968)
    (fuel : Nat) (allowCoins : Bool) :
    execute Late.Check.Normal.checkerImage (1 + fuel) state allowCoins =
      (do let result ← execute Late.Check.Normal.checkerImage fuel (rec_checkPathInitializedState state) allowCoins
          return result.charge 1 0) := by
  have fetched : fetch Late.Check.Normal.checkerImage state = some (.base (.ADDI .x29 .x30 0)) := by
    apply patchedFetch _ 218 _ (by decide) pc; rfl
  have stepped : ordinaryStep state (.base (.ADDI .x29 .x30 0)) =
      some (rec_checkPathInitializedState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      rec_checkPathInitializedState, pc]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

theorem rec_check_path_setup_register (state : MachineState) (reg : Reg) (notCounter : reg ≠ .x29) :
    (rec_checkPathInitializedState state).getReg reg = state.getReg reg := by
  simp only [rec_checkPathInitializedState, MachineState.getReg_setPC,
    MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm notCounter)]

theorem rec_check_path_subroutine (pathDepth : Nat) (depthBound : pathDepth ≤ 24)
    (state : MachineState) (pc : state.pc = 4968)
    (depthReg : state.getReg .x30 = BitVec.ofNat 64 pathDepth)
    (scratch : state.getReg .x21 = 256)
    (sourceValid : ∀ word < 4 * pathDepth,
      accessValid (state.getReg .x25 + BitVec.ofNat 64 (8 * word)) 8 = true)
    (fuel : Nat) (allowCoins : Bool) :
    execute Late.Check.Normal.checkerImage (1 + Late.Check.Normal.pathInstructions (state.getReg .x20) pathDepth + fuel)
        state allowCoins =
      (do let finished ← rec_checkPathLoop (rec_checkPathInitializedState state) pathDepth
          let result ← execute Late.Check.Normal.checkerImage fuel finished allowCoins
          return result.charge (1 + Late.Check.Normal.pathInstructions (state.getReg .x20) pathDepth + 7 * pathDepth) pathDepth) := by
  have initialPC : (rec_checkPathInitializedState state).pc = 4972 := rfl
  have counter : (rec_checkPathInitializedState state).getReg .x29 = BitVec.ofNat 64 pathDepth :=
    depthReg
  have initialScratch := (rec_check_path_setup_register state .x21 (by decide)).trans scratch
  have initialSource : ∀ word < 4 * pathDepth,
      accessValid ((rec_checkPathInitializedState state).getReg .x25 + BitVec.ofNat 64 (8 * word)) 8 = true := by
    rw [rec_check_path_setup_register state .x25 (by decide)]
    exact sourceValid
  rw [Nat.add_assoc, rec_check_path_setup state pc,
    ← rec_check_path_setup_register state .x20 (by decide),
    rec_check_path_loop _ pathDepth depthBound (fun _ => initialPC) counter initialScratch initialSource]
  simp only [bind_assoc, pure_bind, rec_check_path_setup_register state .x20 (by decide)]
  simp [Execution.charge, Nat.add_assoc]

end CommitGolfCandidate.PairCap
