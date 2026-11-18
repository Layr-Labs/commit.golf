import CommitGolfCandidate.CapCountedLoop

/-! Scratch instruction bridges for a possible future nonce proof compactor.
They do not establish a complete loop or a submitted machine certificate. -/
namespace CommitGolfCandidate.NonceWordCopy
set_option maxRecDepth 8192
set_option maxHeartbeats 400000
open CommitGolfCandidate CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

def loadState (state : MachineState) : MachineState :=
  (state.setReg .x6 (state.getMem (state.getReg .x23))).setPC (state.pc+4)

def storeState (state : MachineState) : MachineState :=
  (state.setMem (state.getReg .x25) (state.getReg .x6)).setPC (state.pc+4)

theorem load_execute (image : Image) (state : MachineState) (fuel : Nat)
    (coins : Bool)
    (fetched : fetch image state = some (.base (.LD .x6 .x23 0)))
    (valid : accessValid (state.getReg .x23) 8 = true) :
    execute image (1+fuel) state coins =
      (do let result ← execute image fuel (loadState state) coins
          return result.charge 1 0) := by
  have stepped : ordinaryStep state (.base (.LD .x6 .x23 0)) = some (loadState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      valid, loadState]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

theorem store_execute (image : Image) (state : MachineState) (fuel : Nat)
    (coins : Bool)
    (fetched : fetch image state = some (.base (.SD .x25 .x6 0)))
    (valid : accessValid (state.getReg .x25) 8 = true) :
    execute image (1+fuel) state coins =
      (do let result ← execute image fuel (storeState state) coins
          return result.charge 1 0) := by
  have stepped : ordinaryStep state (.base (.SD .x25 .x6 0)) = some (storeState state) := by
    simp [ordinaryStep, memoryArgumentsValid, memAccess, execInstrBr, signExtend12,
      valid, storeState]
  rw [Nat.add_comm 1 fuel, execute_ordinary_step _ _ _ _ _ _ fetched stepped]
  rfl

theorem copy_memory (state : MachineState) :
    (storeState (loadState state)).mem =
      (state.setMem (state.getReg .x25) (state.getMem (state.getReg .x23))).mem := by
  rfl

theorem copy_execute (image : Image) (state : MachineState) (fuel : Nat)
    (coins : Bool)
    (first : fetch image state = some (.base (.LD .x6 .x23 0)))
    (second : fetch image (loadState state) = some (.base (.SD .x25 .x6 0)))
    (sourceValid : accessValid (state.getReg .x23) 8 = true)
    (targetValid : accessValid (state.getReg .x25) 8 = true) :
    execute image (2+fuel) state coins =
      (do let result ← execute image fuel (storeState (loadState state)) coins
          return result.charge 2 0) := by
  have target : accessValid ((loadState state).getReg .x25) 8 = true := targetValid
  rw [show 2+fuel = 1+(1+fuel) by omega,
    load_execute image state (1+fuel) coins first sourceValid,
    store_execute image (loadState state) fuel coins second target]
  simp [Execution.charge, ← Nat.add_assoc]

theorem copy_target (state : MachineState) :
    (storeState (loadState state)).getMem (state.getReg .x25) =
      state.getMem (state.getReg .x23) := by
  change (storeState (loadState state)).mem (state.getReg .x25) = _
  rw [copy_memory]
  exact MachineState.getMem_setMem_eq

theorem copy_other (state : MachineState) (address : Word)
    (different : address ≠ state.getReg .x25) :
    (storeState (loadState state)).getMem address = state.getMem address := by
  change (storeState (loadState state)).mem address = _
  rw [copy_memory]
  exact MachineState.getMem_setMem_ne different

def copyInstructions (backward : Bool) : List Instr :=
  [.LD .x6 .x23 0, .SD .x25 .x6 0,
   .ADDI .x23 .x23 (if backward then 4088 else 8),
   .ADDI .x25 .x25 (if backward then 4088 else 8),
   .ADDI .x28 .x28 4095, .BNE .x28 .x0 8172]

def copyPrefix (backward : Bool) (state : MachineState) (count : Nat) : MachineState :=
  ((copyInstructions backward).take count).foldl execInstrBr state

theorem copy_prefix_next (backward : Bool) (state : MachineState) (count : Nat)
    (bounded : count < 6) :
    copyPrefix backward state (count+1) =
      execInstrBr (copyPrefix backward state count)
        (((copyInstructions backward)[count]?).getD .EBREAK) := by
  have inside : count < (copyInstructions backward).length := by simpa [copyInstructions] using bounded
  unfold copyPrefix
  rw [List.take_succ_eq_append_getElem inside, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, getElem?_pos (copyInstructions backward) count inside, Option.getD_some]

theorem copy_iteration_execute (image : Image) (backward : Bool) (state : MachineState)
    (fuel : Nat) (coins : Bool)
    (fetched : ∀ count < 6, fetch image (copyPrefix backward state count) =
      some (.base (((copyInstructions backward)[count]?).getD .EBREAK)))
    (sourceValid : accessValid (state.getReg .x23) 8 = true)
    (targetValid : accessValid (state.getReg .x25) 8 = true) :
    execute image (6+fuel) state coins =
      (do let result ← execute image fuel (copyPrefix backward state 6) coins
          return result.charge 6 0) := by
  have source : accessValid (state.regs .x23) 8 = true := sourceValid
  have target : accessValid (state.regs .x25) 8 = true := targetValid
  apply execute_unit_steps (states := copyPrefix backward state)
  intro count bounded
  refine ⟨.base (((copyInstructions backward)[count]?).getD .EBREAK), fetched count bounded, ?_, ?_⟩
  · rw [copy_prefix_next backward state count bounded]
    interval_cases count <;> cases backward <;>
      simp [copyInstructions, copyPrefix, ordinaryStep, memoryArgumentsValid, memAccess,
        execInstrBr, signExtend12, source, target, MachineState.getReg,
        MachineState.setReg, MachineState.setPC]
  · interval_cases count <;> cases backward <;> rfl

private theorem branch_memory (state : MachineState) (offset : BitVec 13) :
    (execInstrBr state (.BNE .x28 .x0 offset)).mem = state.mem := by
  simp only [execInstrBr]
  split <;> rfl

private theorem branch_register (state : MachineState) (offset : BitVec 13) (reg : Reg) :
    (execInstrBr state (.BNE .x28 .x0 offset)).getReg reg = state.getReg reg := by
  simp only [execInstrBr]
  split <;> exact MachineState.getReg_setPC

theorem iteration_memory (backward : Bool) (state : MachineState) :
    (copyPrefix backward state 6).mem =
      (state.setMem (state.getReg .x25) (state.getMem (state.getReg .x23))).mem := by
  rw [show 6=5+1 by rfl, copy_prefix_next backward state 5 (by decide)]
  change (execInstrBr (copyPrefix backward state 5) (.BNE .x28 .x0 8172)).mem = _
  rw [branch_memory]
  simp [copyPrefix, copyInstructions, execInstrBr, signExtend12, MachineState.setPC,
    MachineState.setReg, MachineState.setMem, MachineState.getReg, MachineState.getMem]

theorem iteration_source (backward : Bool) (state : MachineState) :
    (copyPrefix backward state 6).getReg .x23 = state.getReg .x23 +
      signExtend12 (if backward then 4088 else 8) := by
  rw [show 6=5+1 by rfl, copy_prefix_next backward state 5 (by decide)]
  change (execInstrBr (copyPrefix backward state 5) (.BNE .x28 .x0 8172)).getReg .x23 = _
  rw [branch_register]
  rfl

theorem iteration_target (backward : Bool) (state : MachineState) :
    (copyPrefix backward state 6).getReg .x25 = state.getReg .x25 +
      signExtend12 (if backward then 4088 else 8) := by
  rw [show 6=5+1 by rfl, copy_prefix_next backward state 5 (by decide)]
  change (execInstrBr (copyPrefix backward state 5) (.BNE .x28 .x0 8172)).getReg .x25 = _
  rw [branch_register]
  rfl

theorem iteration_counter (backward : Bool) (state : MachineState) :
    (copyPrefix backward state 6).getReg .x28 = state.getReg .x28 + signExtend12 4095 := by
  rw [show 6=5+1 by rfl, copy_prefix_next backward state 5 (by decide)]
  change (execInstrBr (copyPrefix backward state 5) (.BNE .x28 .x0 8172)).getReg .x28 = _
  rw [branch_register]
  rfl

theorem prefix_pc (backward : Bool) (state : MachineState) (count : Nat)
    (bounded : count ≤ 5) :
    (copyPrefix backward state count).pc = state.pc + BitVec.ofNat 64 (4*count) := by
  interval_cases count <;> cases backward <;>
    simp [copyPrefix, copyInstructions, execInstrBr, MachineState.setPC,
      MachineState.setReg, MachineState.setMem, BitVec.add_assoc]

theorem decrement (count : Nat) (positive : 0<count) :
    BitVec.ofNat 64 count + signExtend12 (4095 : BitVec 12) =
      BitVec.ofNat 64 (count-1) := by
  rw [show signExtend12 (4095 : BitVec 12) = -(1 : Word) by decide]
  have equation : count=count-1+1 := by omega
  conv_lhs => rw [equation]
  rw [BitVec.ofNat_add, BitVec.add_assoc]
  simp

theorem iteration_pc (backward : Bool) (state : MachineState) (count : Nat)
    (positive : 0<count) (bounded : count<2^64)
    (counter : state.getReg .x28 = BitVec.ofNat 64 count) :
    (copyPrefix backward state 6).pc = if count=1 then state.pc+24 else state.pc := by
  have nextCounter := iteration_counter backward state
  rw [show 6=5+1 by rfl, copy_prefix_next backward state 5 (by decide)] at nextCounter
  change (execInstrBr (copyPrefix backward state 5) (.BNE .x28 .x0 8172)).getReg .x28 = _ at nextCounter
  rw [branch_register, counter, decrement count positive] at nextCounter
  rw [show 6=5+1 by rfl, copy_prefix_next backward state 5 (by decide)]
  change (execInstrBr (copyPrefix backward state 5) (.BNE .x28 .x0 8172)).pc = _
  simp only [execInstrBr, nextCounter, prefix_pc backward state 5 (by decide)]
  have zero : (copyPrefix backward state 5).getReg .x0 = 0 := rfl
  rw [zero]
  have back : state.pc+20+signExtend13 (8172 : BitVec 13)=state.pc := by
    rw [show signExtend13 (8172 : BitVec 13) = -(20 : Word) by decide]
    simp [BitVec.add_assoc]
  have exit : state.pc+20+4=state.pc+24 := by rw [BitVec.add_assoc]; rfl
  by_cases last : count=1
  · subst count
    simp only [Nat.sub_self, show BitVec.ofNat 64 0=(0:Word) by rfl,
      bne_self_eq_false, Bool.false_eq_true, ite_false, ite_true, MachineState.setPC]
    exact exit
  · have nonzero : BitVec.ofNat 64 (count-1) ≠ (0:Word) := by
      intro equal
      have numeric := congrArg BitVec.toNat equal
      change (count-1)%2^64=0 at numeric
      rw [Nat.mod_eq_of_lt (by omega)] at numeric
      omega
    simp only [if_neg last, bne_iff_ne, ne_eq, nonzero, not_false_eq_true,
      ite_true, MachineState.setPC]
    exact back

theorem prefix_register (backward : Bool) (state : MachineState) (count : Nat)
    (bounded : count ≤ 6) (reg : Reg)
    (outside : reg ≠ .x6 ∧ reg ≠ .x23 ∧ reg ≠ .x25 ∧ reg ≠ .x28) :
    (copyPrefix backward state count).getReg reg=state.getReg reg := by
  have memory (current : MachineState) (location value : Word) :
      (current.setMem location value).getReg reg=current.getReg reg := by
    cases reg <;> rfl
  have step (current : MachineState) (index : Nat) (inside : index<6) :
      (execInstrBr current (((copyInstructions backward)[index]?).getD .EBREAK)).getReg reg=
        current.getReg reg := by
    interval_cases index <;>
      simp only [copyInstructions, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Option.getD_some, execInstrBr, MachineState.getReg_setPC]
    · exact MachineState.getReg_setReg_ne current .x6 reg _ (Ne.symm outside.1)
    · exact memory _ _ _
    · exact MachineState.getReg_setReg_ne current .x23 reg _ (Ne.symm outside.2.1)
    · exact MachineState.getReg_setReg_ne current .x25 reg _ (Ne.symm outside.2.2.1)
    · exact MachineState.getReg_setReg_ne current .x28 reg _ (Ne.symm outside.2.2.2)
    · split <;> exact MachineState.getReg_setPC
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [copy_prefix_next backward state count (by omega), step _ count (by omega), ih (by omega)]

theorem loop_register (backward : Bool) (state : MachineState) (count : Nat)
    (reg : Reg) (outside : reg ≠ .x6 ∧ reg ≠ .x23 ∧ reg ≠ .x25 ∧ reg ≠ .x28) :
    (capCountedRun (fun current => copyPrefix backward current 6) count state).getReg reg=
      state.getReg reg := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
    rw [capCountedRun, ih, prefix_register backward state 6 (by decide) reg outside]

end CommitGolfCandidate.NonceWordCopy
