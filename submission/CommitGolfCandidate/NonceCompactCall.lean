import CommitGolfCandidate.NonceCompactHeader

/-! Calls to the shared copy routine in the concrete compactor. The second
call advances past the omitted padding word before copying the sibling words. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

def nonceCompactCallInstructions (siblings : Bool) : List Instr :=
  if siblings then [.ADDI .x23 .x23 8, .ADDI .x28 .x0 64, .JAL .x1 44]
  else [.ADDI .x28 .x0 3, .JAL .x1 56]

def nonceCompactCallPrefix (siblings : Bool) (state : MachineState) (count : Nat) : MachineState :=
  ((nonceCompactCallInstructions siblings).take count).foldl execInstrBr state

abbrev nonceCompactCallCount (siblings : Bool) : Nat := if siblings then 3 else 2

abbrev nonceCompactCallEntry (siblings : Bool) : Word := if siblings then 4568 else 4560

private def nonceCompactMachineCallInstructions (siblings : Bool) : List Instr :=
  if siblings then nonceCompactCallInstructions true else [.ADDI .x28 .x0 3, .JAL .x1 84]

private def nonceCompactMachineCallPrefix (siblings : Bool) (state : MachineState)
    (count : Nat) : MachineState :=
  ((nonceCompactMachineCallInstructions siblings).take count).foldl execInstrBr state

/-- The short nonce call retains the reference registers and link, and enters
the specialized helper appended after the shared copy routine. -/
def nonceCompactMachineCallState (siblings : Bool) (state : MachineState) : MachineState :=
  let reference := nonceCompactCallPrefix siblings state (nonceCompactCallCount siblings)
  if siblings then reference else reference.setPC 4648

private theorem nonce_compact_machine_call_state (siblings : Bool) (state : MachineState)
    (pc : state.pc=nonceCompactCallEntry siblings) :
    nonceCompactMachineCallPrefix siblings state (nonceCompactCallCount siblings)=
      nonceCompactMachineCallState siblings state := by
  cases siblings
  · simp [nonceCompactCallEntry] at pc
    simp [nonceCompactMachineCallPrefix, nonceCompactMachineCallInstructions,
      nonceCompactMachineCallState, nonceCompactCallPrefix, nonceCompactCallCount,
      nonceCompactCallInstructions, execInstrBr, signExtend21, MachineState.setPC, pc]
  · rfl

private theorem nonce_compact_call_fetch (siblings : Bool) (state : MachineState)
    (pc : state.pc=nonceCompactCallEntry siblings) (count : Nat)
    (bounded : count < nonceCompactCallCount siblings) :
    fetch nonceCompactImage (nonceCompactMachineCallPrefix siblings state count)=
      some (.base (((nonceCompactMachineCallInstructions siblings)[count]?).getD .EBREAK)) := by
  cases siblings with
  | false =>
    change count < 2 at bounded
    change state.pc=4560 at pc
    apply cap_image_fetch _ _ (116+count) _ (by omega)
    · interval_cases count <;>
        simp [nonceCompactMachineCallPrefix, nonceCompactMachineCallInstructions, execInstrBr,
          MachineState.setPC, pc, nonceCompactCallInstructions] <;> rfl
    · interval_cases count <;> rfl
  | true =>
    change count < 3 at bounded
    change state.pc=4568 at pc
    apply cap_image_fetch _ _ (118+count) _ (by omega)
    · interval_cases count <;>
        simp [nonceCompactMachineCallPrefix, nonceCompactMachineCallInstructions, execInstrBr,
          MachineState.setPC, pc, nonceCompactCallInstructions] <;> rfl
    · interval_cases count <;> rfl

theorem nonce_compact_call_execute (siblings : Bool) (state : MachineState)
    (pc : state.pc=nonceCompactCallEntry siblings) (fuel : Nat) (coins : Bool) :
    execute nonceCompactImage (nonceCompactCallCount siblings+fuel) state coins=
      (do let result ← execute nonceCompactImage fuel
            (nonceCompactMachineCallState siblings state) coins
          return result.charge (nonceCompactCallCount siblings) 0) := by
  rw [← nonce_compact_machine_call_state siblings state pc]
  apply execute_unit_steps (states := nonceCompactMachineCallPrefix siblings state)
  intro count bounded
  refine ⟨.base (((nonceCompactMachineCallInstructions siblings)[count]?).getD .EBREAK),
    nonce_compact_call_fetch siblings state pc count bounded, ?_, ?_⟩
  · cases siblings with
    | false =>
      change count < 2 at bounded
      interval_cases count <;> rfl
    | true =>
      change count < 3 at bounded
      interval_cases count <;> rfl
  · cases siblings with
    | false =>
      change count < 2 at bounded
      interval_cases count <;> rfl
    | true =>
      change count < 3 at bounded
      interval_cases count <;> rfl

theorem nonce_compact_call_memory (siblings : Bool) (state : MachineState) :
    (nonceCompactCallPrefix siblings state (nonceCompactCallCount siblings)).mem=state.mem := by
  cases siblings <;> rfl

theorem nonce_compact_call_control (siblings : Bool) (state : MachineState)
    (pc : state.pc=nonceCompactCallEntry siblings) :
    let final := nonceCompactCallPrefix siblings state (nonceCompactCallCount siblings)
    final.pc=4620 ∧ final.getReg .x28=(if siblings then 64 else 3) ∧
    final.getReg .x1=(if siblings then 4580 else 4568) := by
  cases siblings <;>
    simp [nonceCompactCallEntry] at pc <;>
    simp [nonceCompactCallPrefix, nonceCompactCallInstructions, nonceCompactCallCount,
      execInstrBr, MachineState.setPC, MachineState.getReg, MachineState.setReg, pc,
      signExtend12, signExtend21]

theorem nonce_compact_call_source (siblings : Bool) (state : MachineState) :
    (nonceCompactCallPrefix siblings state (nonceCompactCallCount siblings)).getReg .x23=
      state.getReg .x23+(if siblings then 8 else 0) := by
  cases siblings <;>
    simp [nonceCompactCallPrefix, nonceCompactCallInstructions, nonceCompactCallCount,
      execInstrBr, MachineState.setPC, MachineState.getReg, MachineState.setReg, signExtend12]

theorem nonce_compact_call_register (siblings : Bool) (state : MachineState) (reg : Reg)
    (outside : reg ≠ .x1 ∧ reg ≠ .x23 ∧ reg ≠ .x28) :
    (nonceCompactCallPrefix siblings state (nonceCompactCallCount siblings)).getReg reg=
      state.getReg reg := by
  cases siblings <;> cases reg <;>
    simp_all [nonceCompactCallPrefix, nonceCompactCallInstructions, nonceCompactCallCount,
      execInstrBr, MachineState.setPC, MachineState.getReg, MachineState.setReg]

end CommitGolfCandidate
