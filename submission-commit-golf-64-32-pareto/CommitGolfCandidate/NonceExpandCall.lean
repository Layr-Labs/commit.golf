import CommitGolfCandidate.NonceCopyProcedure

/-! Real calls in one checker expansion record. Siblings move high-to-low
first; the second call writes the omitted zero padding word, backs up the
destination once more and copies the three nonce words. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

def nonceExpandCallInstructions (nonce : Bool) : List Instr :=
  if nonce then [.SD .x25 .x0 0,.ADDI .x25 .x25 4088,.ADDI .x28 .x0 3,.JAL .x1 60]
  else [.ADDI .x28 .x0 64,.JAL .x1 76]

abbrev nonceExpandCallCount (nonce : Bool) : Nat := if nonce then 4 else 2
abbrev nonceExpandCallEntry (nonce : Bool) : Word := if nonce then 5024 else 5016

def nonceExpandCallPrefix (nonce : Bool) (state : MachineState) (count : Nat) : MachineState :=
  ((nonceExpandCallInstructions nonce).take count).foldl execInstrBr state

theorem nonce_expand_call_fetch (nonce : Bool) (state : MachineState)
    (pc : state.pc=nonceExpandCallEntry nonce) (count : Nat) (bounded : count<nonceExpandCallCount nonce) :
    fetch nonceExpandedImage (nonceExpandCallPrefix nonce state count)=
      some (.base (((nonceExpandCallInstructions nonce)[count]?).getD .EBREAK)) := by
  cases nonce with
  | false =>
    change count<2 at bounded
    change state.pc=5016 at pc
    apply cap_image_fetch _ _ (230+count) _ (by omega)
    · interval_cases count <;>
        simp [nonceExpandCallPrefix,nonceExpandCallInstructions,execInstrBr,MachineState.setPC,pc]
    · interval_cases count <;> rfl
  | true =>
    change count<4 at bounded
    change state.pc=5024 at pc
    apply cap_image_fetch _ _ (232+count) _ (by omega)
    · interval_cases count <;>
        simp [nonceExpandCallPrefix,nonceExpandCallInstructions,execInstrBr,MachineState.setPC,
          MachineState.setMem,pc]
    · interval_cases count <;> rfl

theorem nonce_expand_call_execute (nonce : Bool) (state : MachineState)
    (pc : state.pc=nonceExpandCallEntry nonce)
    (paddingValid : nonce=true → accessValid (state.getReg .x25) 8=true)
    (fuel : Nat) (coins : Bool) :
    execute nonceExpandedImage (nonceExpandCallCount nonce+fuel) state coins=
      (do let result ← execute nonceExpandedImage fuel
            (nonceExpandCallPrefix nonce state (nonceExpandCallCount nonce)) coins
          return result.charge (nonceExpandCallCount nonce) 0) := by
  apply execute_unit_steps (states := nonceExpandCallPrefix nonce state)
  intro count bounded
  refine ⟨.base (((nonceExpandCallInstructions nonce)[count]?).getD .EBREAK),
    nonce_expand_call_fetch nonce state pc count bounded,?_,?_⟩
  · cases nonce with
    | false => change count<2 at bounded; interval_cases count <;> rfl
    | true =>
      change count<4 at bounded
      have valid:=paddingValid rfl
      interval_cases count
      · simp [ordinaryStep,memoryArgumentsValid,memAccess,nonceExpandCallPrefix,
          nonceExpandCallInstructions,execInstrBr,signExtend12,valid]
      all_goals rfl
  · cases nonce with
    | false => change count<2 at bounded; interval_cases count <;> rfl
    | true => change count<4 at bounded; interval_cases count <;> rfl

theorem nonce_expand_call_control (nonce : Bool) (state : MachineState)
    (pc : state.pc=nonceExpandCallEntry nonce) :
    let final := nonceExpandCallPrefix nonce state (nonceExpandCallCount nonce)
    final.pc=5096 ∧ final.getReg .x28=(if nonce then 3 else 64) ∧
      final.getReg .x1=(if nonce then 5040 else 5024) := by
  cases nonce <;> simp [nonceExpandCallEntry] at pc <;>
    simp [nonceExpandCallPrefix,nonceExpandCallInstructions,nonceExpandCallCount,execInstrBr,
      MachineState.setPC,MachineState.setReg,MachineState.setMem,MachineState.getReg,
      signExtend12,signExtend21,pc]

theorem nonce_expand_call_register (nonce : Bool) (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x1 ∧ reg ≠ .x25 ∧ reg ≠ .x28) :
    (nonceExpandCallPrefix nonce state (nonceExpandCallCount nonce)).getReg reg=state.getReg reg := by
  cases nonce <;> cases reg <;>
    simp_all [nonceExpandCallPrefix,nonceExpandCallInstructions,nonceExpandCallCount,
      execInstrBr,MachineState.setPC,MachineState.setReg,MachineState.setMem,MachineState.getReg]

theorem nonce_expand_call_memory (nonce : Bool) (state : MachineState) :
    (nonceExpandCallPrefix nonce state (nonceExpandCallCount nonce)).mem=
      if nonce then (state.setMem (state.getReg .x25) 0).mem else state.mem := by
  cases nonce <;>
    simp [nonceExpandCallPrefix,nonceExpandCallInstructions,nonceExpandCallCount,execInstrBr,
      MachineState.setPC,MachineState.setReg,MachineState.setMem,MachineState.getReg,signExtend12]

end CommitGolfCandidate
