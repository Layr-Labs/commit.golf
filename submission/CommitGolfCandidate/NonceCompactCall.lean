import CommitGolfCandidate.NonceCompactHeader

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

theorem nonce_compact_call_fetch (siblings : Bool) (state : MachineState)
    (pc : state.pc=nonceCompactCallEntry siblings) (count : Nat)
    (bounded : count < nonceCompactCallCount siblings) :
    fetch nonceCompactImage (nonceCompactCallPrefix siblings state count)=
      some (.base (((nonceCompactCallInstructions siblings)[count]?).getD .EBREAK)) := by
  cases siblings with
  | false =>
    change count < 2 at bounded
    change state.pc=4560 at pc
    apply cap_image_fetch _ _ (116+count) _ (by omega)
    · interval_cases count <;>
        simp [nonceCompactCallPrefix, nonceCompactCallInstructions, execInstrBr,
          MachineState.setPC, pc] <;> rfl
    · interval_cases count <;> rfl
  | true =>
    change count < 3 at bounded
    change state.pc=4568 at pc
    apply cap_image_fetch _ _ (118+count) _ (by omega)
    · interval_cases count <;>
        simp [nonceCompactCallPrefix, nonceCompactCallInstructions, execInstrBr,
          MachineState.setPC, pc] <;> rfl
    · interval_cases count <;> rfl

theorem nonce_compact_call_execute (siblings : Bool) (state : MachineState)
    (pc : state.pc=nonceCompactCallEntry siblings) (fuel : Nat) (coins : Bool) :
    execute nonceCompactImage (nonceCompactCallCount siblings+fuel) state coins=
      (do let result ← execute nonceCompactImage fuel
            (nonceCompactCallPrefix siblings state (nonceCompactCallCount siblings)) coins
          return result.charge (nonceCompactCallCount siblings) 0) := by
  apply execute_unit_steps (states := nonceCompactCallPrefix siblings state)
  intro count bounded
  refine ⟨.base (((nonceCompactCallInstructions siblings)[count]?).getD .EBREAK),
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
