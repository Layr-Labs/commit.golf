import CommitGolfCandidate.Commit
import CommitGolfCandidate.WriteMemory

/-! Bottom-up parent construction and successful commitment return. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

abbrev commitParentQuery (state : MachineState) : PublicSpec.Domain :=
  .inl (readBuffer state (state.getReg .x9 + (state.getReg .x20 <<< 6)).toNat 64)

/-- The fixed parent syscall arguments are initialized once per tree. -/
def ParentOracleReady (state : MachineState) : Prop :=
  state.getReg .x5 = 0 ∧ state.getReg .x11 = 64 ∧ state.getReg .x13 = 0

private def parentArgInstructions : List Instr :=
  [.ADDI .x5 .x0 0, .ADDI .x11 .x0 64, .ADDI .x13 .x0 0]

private def parentArgPrefix (state : MachineState) (count : Nat) : MachineState :=
  (parentArgInstructions.take count).foldl execInstrBr state

def commitParentArgsState (state : MachineState) : MachineState := parentArgPrefix state 3

@[simp] theorem parent_args_register (state : MachineState) (reg : Reg)
    (preserved : reg ∉ [.x5,.x11,.x13]) :
    (commitParentArgsState state).getReg reg = state.getReg reg := by
  cases reg <;> simp_all [commitParentArgsState,parentArgPrefix,parentArgInstructions,
    execInstrBr,signExtend12,MachineState.getReg,MachineState.setReg,MachineState.setPC]

@[simp] theorem parent_args_pc (state : MachineState) :
    (commitParentArgsState state).pc = state.pc + 12 := by
  simp [commitParentArgsState,parentArgPrefix,parentArgInstructions,execInstrBr,
    MachineState.setPC,BitVec.add_assoc]

@[simp] theorem parent_args_ready (state : MachineState) :
    ParentOracleReady (commitParentArgsState state) := by
  simp [ParentOracleReady,commitParentArgsState,parentArgPrefix,parentArgInstructions,
    execInstrBr,signExtend12,MachineState.getReg,MachineState.setReg,MachineState.setPC]

theorem commit_parent_args (state : MachineState) (pc : state.pc = 4348) (fuel : Nat) :
    execute (submission.image .commit) (3 + fuel) state true =
      (do let result ← execute (submission.image .commit) fuel (commitParentArgsState state) true
          return result.charge 3 0) := by
  apply execute_unit_steps (states := parentArgPrefix state)
  intro i hi
  refine ⟨.base ((parentArgInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply commit_fetch _ (63+i) _ (by omega)
    · interval_cases i <;> simp [parentArgPrefix,parentArgInstructions,execInstrBr,pc,MachineState.setPC]
    · interval_cases i <;> rfl
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

private def parentInstructions : List Instr :=
  [.SLLI .x6 .x20 6, .ADD .x10 .x9 .x6, .SLLI .x7 .x20 5, .ADD .x12 .x9 .x7,
   .ADDI .x5 .x0 0, .ADDI .x11 .x0 64, .ADDI .x13 .x0 0]

private def parentPrefix (state : MachineState) (count : Nat) : MachineState :=
  (parentInstructions.take count).foldl execInstrBr state

def commitParentState (state : MachineState) (answer : BitVec 256) : MachineState :=
  writeBits (parentPrefix state 7) (state.getReg .x9 + (state.getReg .x20 <<< 5)) answer

/-- The parent's setup instructions do not change memory; its only write is the
compression reply at the parent heap slot. -/
theorem commit_parent_written_memory (state : MachineState) (answer : BitVec 256) :
    (commitParentState state answer).mem =
      (writeBits state (state.getReg .x9+(state.getReg .x20 <<< 5)) answer).mem :=
  write_bits_memory_congr _ state _ answer rfl

private def parentPointerPrefix (state : MachineState) (count : Nat) : MachineState :=
  ((parentInstructions.take 4).take count).foldl execInstrBr state

private theorem parent_prefix_ready (state : MachineState) (ready : ParentOracleReady state) :
    parentPrefix state 7 = (parentPointerPrefix state 4).setPC (state.pc + 28) := by
  cases state with
  | mk regs mem code pc committed publicValues privateInput inputBufBase =>
    dsimp [ParentOracleReady,MachineState.getReg] at ready
    dsimp [parentPrefix,parentPointerPrefix,parentInstructions,List.take,List.foldl,
      execInstrBr,signExtend12,MachineState.getReg,MachineState.setReg,MachineState.setPC]
    congr 1
    · funext reg
      cases reg <;> simp_all
    · simp [BitVec.add_assoc]

theorem hoist_fixed_compression_input (state : MachineState) (source destination : Word)
    (r10 : state.getReg .x10 = source) (r11 : state.getReg .x11 = 64)
    (r12 : state.getReg .x12 = destination) (r13 : state.getReg .x13 = 0)
    (sourceValid : rangeValid source 64 = true) (destinationValid : rangeValid destination 32 = true)
    (sourceAligned : source.toNat % 8 = 0) (destinationAligned : destination.toNat % 8 = 0) :
    oracleInput state = some (.inl (readBuffer state source.toNat 64)) := by
  have kind : (state.getReg .x13).toNat = 0 := by rw [r13]; rfl
  unfold oracleInput
  simp only [kind]
  simp [r10,r11,r12,COMPRESSION_INPUT_LENGTH,COMPRESSION_OUTPUT_LENGTH,
    sourceValid,destinationValid,sourceAligned,destinationAligned]
  exact hoist_read_width state source.toNat _ kind

/-- Four pointer instructions and one syscall process a parent after hoisting arguments. -/
theorem commit_parent_compression (state : MachineState) (pc : state.pc = 4360)
    (ready : ParentOracleReady state)
    (sourceValid : rangeValid (state.getReg .x9 + (state.getReg .x20 <<< 6)) 64 = true)
    (destinationValid : rangeValid (state.getReg .x9 + (state.getReg .x20 <<< 5)) 32 = true)
    (sourceAligned : (state.getReg .x9 + (state.getReg .x20 <<< 6)).toNat % 8 = 0)
    (destinationAligned : (state.getReg .x9 + (state.getReg .x20 <<< 5)).toNat % 8 = 0)
    (fuel : Nat) :
    execute (submission.image .commit) (5 + fuel) state true =
      (do let answer ← World.query (.inr (commitParentQuery state))
          let result ← execute (submission.image .commit) fuel
            ((commitParentState state answer).setPC 4380) true
          return result.charge 12 1) := by
  have setup (remaining : Nat) :
      execute (submission.image .commit) (4 + remaining) state true =
        (do let result ← execute (submission.image .commit) remaining (parentPointerPrefix state 4) true
            return result.charge 4 0) := by
    apply execute_unit_steps (states := parentPointerPrefix state)
    intro i hi
    refine ⟨.base (((parentInstructions.take 4)[i]?).getD .EBREAK), ?_, ?_, ?_⟩
    · apply commit_fetch _ (66+i) _ (by omega)
      · interval_cases i <;> simp [parentPointerPrefix,parentInstructions,execInstrBr,pc,MachineState.setPC]
      · interval_cases i <;> rfl
    · interval_cases i <;> rfl
    · interval_cases i <;> rfl
  let current := parentPointerPrefix state 4
  have fetched : fetch (submission.image .commit) current = some (.base .ECALL) := by
    apply commit_fetch _ 70 _ (by decide)
    · simp [current,parentPointerPrefix,parentInstructions,execInstrBr,pc,MachineState.setPC]
    · rfl
  have registers : current.getReg .x5 = 0 ∧
      current.getReg .x10 = state.getReg .x9 + (state.getReg .x20 <<< 6) ∧
      current.getReg .x11 = 64 ∧ current.getReg .x12 = state.getReg .x9 + (state.getReg .x20 <<< 5) ∧
      current.getReg .x13 = 0 := by
    rcases ready with ⟨r5,r11,r13⟩
    have r5' : state.regs .x5 = 0 := r5
    have r11' : state.regs .x11 = 64 := r11
    have r13' : state.regs .x13 = 0 := r13
    simp [current,parentPointerPrefix,parentInstructions,execInstrBr,signExtend12,
      MachineState.getReg,MachineState.setReg,MachineState.setPC,r5',r11',r13']
  have memory (address : Nat) : readBuffer current address 64 = readBuffer state address 64 := rfl
  have input : oracleInput current = some (commitParentQuery state) := by
    have fixed := hoist_fixed_compression_input current
      (state.getReg .x9 + (state.getReg .x20 <<< 6))
      (state.getReg .x9 + (state.getReg .x20 <<< 5))
      registers.2.1 registers.2.2.1 registers.2.2.2.1 registers.2.2.2.2
      sourceValid destinationValid sourceAligned destinationAligned
    simpa only [commitParentQuery,memory] using fixed
  have normalized (answer : BitVec 256) :
      (commitParentState state answer).setPC 4380 =
        writeBits current (state.getReg .x9 + (state.getReg .x20 <<< 5)) answer := by
    rw [commitParentState,parent_prefix_ready state ready,hoist_write_bits_pc,hoist_pc_pc]
    have outputpc : (writeBits current (state.getReg .x9 + (state.getReg .x20 <<< 5)) answer).pc = 4380 := by
      change current.pc + 4 = 4380
      simp [current,parentPointerPrefix,parentInstructions,execInstrBr,MachineState.setPC,pc]
    rw [← outputpc,hoist_pc_self]
  rw [show 5 + fuel = 4 + (fuel + 1) by omega,setup,execute,fetched,
    if_pos registers.1,input]
  simp only [commitParentQuery,writeOracleAnswer,registers.2.2.2.1,oracleCycles,COMPRESSION_CYCLES,
    bind_assoc,pure_bind]
  apply congrArg (fun continuation =>
    (liftM (World.query (.inr (commitParentQuery state))) : OracleComp World (BitVec 256)) >>= continuation)
  funext answer
  rw [registers.2.2.2.1,normalized answer]
  simp [Execution.charge,← Nat.add_assoc]
  rfl

theorem commit_parent_pc (state : MachineState) (answer : BitVec 256) :
    (commitParentState state answer).pc = state.pc + 32 := by
  simp [commitParentState, writeBits, parentPrefix, parentInstructions, execInstrBr,
    MachineState.setPC, BitVec.add_assoc]

theorem commit_parent_register (state : MachineState) (answer : BitVec 256) (reg : Reg)
    (preserved : reg ∈ [Reg.x9, .x19, .x20, .x21, .x26]) :
    (commitParentState state answer).getReg reg = state.getReg reg := by
  rw [commitParentState, writeBits_register]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at preserved
  rcases preserved with rfl | rfl | rfl | rfl | rfl <;>
    simp [parentPrefix, parentInstructions,
      execInstrBr, MachineState.getReg, MachineState.setReg, MachineState.setPC]

def commitParentNextState (state : MachineState) : MachineState :=
  (state.setReg .x20 (state.getReg .x20 - 1)).setPC
    (if state.getReg .x20 - 1 = 0 then 4388 else 4360)

theorem commit_parent_next_pc_irrel (state : MachineState) (pc : Word) :
    commitParentNextState (state.setPC pc) = commitParentNextState state := by
  cases state; rfl

/-- The reference parent step establishes the invariant for subsequent nodes. -/
theorem commit_parent_ready (state : MachineState) (answer : BitVec 256) :
    ParentOracleReady (commitParentNextState (commitParentState state answer)) := by
  change ParentOracleReady (commitParentState state answer)
  have registers : ParentOracleReady (parentPrefix state 7) := by
    simp [ParentOracleReady,parentPrefix,parentInstructions,execInstrBr,signExtend12,
      MachineState.getReg,MachineState.setReg,MachineState.setPC]
  unfold ParentOracleReady at registers ⊢
  simpa only [commitParentState,writeBits_register] using registers

theorem commit_parent_next (state : MachineState) (pc : state.pc = 4380) (fuel : Nat) :
    execute (submission.image .commit) (2 + fuel) state true =
      (do let result ← execute (submission.image .commit) fuel (commitParentNextState state) true
          return result.charge 2 0) := by
  let next := (state.setReg .x20 (state.getReg .x20 - 1)).setPC 4384
  have f0 : fetch (submission.image .commit) state = some (.base (.ADDI .x20 .x20 4095)) := by
    apply commit_fetch _ 71 _ (by decide) pc; rfl
  have f1 : fetch (submission.image .commit) next = some (.base (.BNE .x20 .x0 8168)) := by
    apply commit_fetch _ 72 _ (by decide) rfl; rfl
  have s0 : ordinaryStep state (.base (.ADDI .x20 .x20 4095)) = some next := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      next, pc, BitVec.sub_eq_add_neg]
  have s1 : ordinaryStep next (.base (.BNE .x20 .x0 8168)) = some (commitParentNextState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend13,
      next, commitParentNextState, MachineState.getReg, MachineState.setReg, MachineState.setPC]
    split <;> simp_all
  rw [show 2 + fuel = (fuel + 1) + 1 by omega,
    execute_ordinary_step _ _ _ _ _ _ f0 s0, execute_ordinary_step _ _ _ _ _ _ f1 s1]
  simp [instructionCycles, Execution.charge, ← Nat.add_assoc]

/-- One parent costs fourteen cycles and one public query. -/
theorem commit_parent (state : MachineState) (pc : state.pc = 4360)
    (ready : ParentOracleReady state)
    (sourceValid : rangeValid (state.getReg .x9 + (state.getReg .x20 <<< 6)) 64 = true)
    (destinationValid : rangeValid (state.getReg .x9 + (state.getReg .x20 <<< 5)) 32 = true)
    (sourceAligned : (state.getReg .x9 + (state.getReg .x20 <<< 6)).toNat % 8 = 0)
    (destinationAligned : (state.getReg .x9 + (state.getReg .x20 <<< 5)).toNat % 8 = 0)
    (fuel : Nat) :
    execute (submission.image .commit) (7 + fuel) state true =
      (do let answer ← World.query (.inr (commitParentQuery state))
          let result ← execute (submission.image .commit) fuel
            (commitParentNextState (commitParentState state answer)) true
          return result.charge 14 1) := by
  rw [show 7 + fuel = 5 + (2 + fuel) by omega,
    commit_parent_compression state pc ready sourceValid destinationValid sourceAligned destinationAligned]
  apply congrArg (fun continuation =>
    (liftM (World.query (.inr (commitParentQuery state))) :
      OracleComp World (BitVec 256)) >>= continuation)
  funext answer
  change BitVec 256 at answer
  have nextPC : ((commitParentState state answer).setPC 4380).pc = 4380 := rfl
  rw [commit_parent_next _ nextPC]
  simp [commit_parent_next_pc_irrel, Execution.charge, ← Nat.add_assoc]

end CommitGolfCandidate
