import CommitGolfCandidate.NonceCopyProcedure

/-! The concrete compactor entry saves the old output end and initializes both
copy pointers and the record count. This bridge charges its four real moves. -/
namespace CommitGolfCandidate
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

def nonceCompactHeaderInstructions : List Instr :=
  [.ADDI .x22 .x25 0, .ADDI .x23 .x15 0, .ADDI .x25 .x15 0,
    .ADDI .x24 .x16 0]

def nonceCompactHeaderPrefix (state : MachineState) (count : Nat) : MachineState :=
  (nonceCompactHeaderInstructions.take count).foldl execInstrBr state

theorem nonce_compact_header_pc (state : MachineState) (count : Nat) (bounded : count ≤ 4) :
    (nonceCompactHeaderPrefix state count).pc=state.pc+BitVec.ofNat 64 (4*count) := by
  interval_cases count <;> simp [nonceCompactHeaderPrefix, nonceCompactHeaderInstructions,
    execInstrBr, MachineState.setPC, BitVec.add_assoc]

theorem nonce_compact_header_fetch (state : MachineState) (pc : state.pc=4540)
    (count : Nat) (bounded : count < 4) :
    fetch nonceCompactImage (nonceCompactHeaderPrefix state count)=
      some (.base ((nonceCompactHeaderInstructions[count]?).getD .EBREAK)) := by
  apply cap_image_fetch _ _ (111+count) _ (by omega)
  · rw [nonce_compact_header_pc state count (by omega), pc]
    interval_cases count <;> rfl
  · interval_cases count <;> rfl

theorem nonce_compact_header_execute (state : MachineState) (pc : state.pc=4540)
    (fuel : Nat) (coins : Bool) :
    execute nonceCompactImage (4+fuel) state coins=
      (do let result ← execute nonceCompactImage fuel (nonceCompactHeaderPrefix state 4) coins
          return result.charge 4 0) := by
  apply execute_unit_steps (states := nonceCompactHeaderPrefix state)
  intro count bounded
  refine ⟨.base ((nonceCompactHeaderInstructions[count]?).getD .EBREAK),
    nonce_compact_header_fetch state pc count bounded, ?_, ?_⟩
  · interval_cases count <;> rfl
  · interval_cases count <;> rfl

theorem nonce_compact_header_memory (state : MachineState) :
    (nonceCompactHeaderPrefix state 4).mem=state.mem := rfl

theorem nonce_compact_header_registers (state : MachineState) :
    let final := nonceCompactHeaderPrefix state 4
    final.getReg .x22=state.getReg .x25 ∧
    final.getReg .x23=state.getReg .x15 ∧
    final.getReg .x25=state.getReg .x15 ∧
    final.getReg .x24=state.getReg .x16 := by
  simp [nonceCompactHeaderPrefix, nonceCompactHeaderInstructions, execInstrBr,
    signExtend12, MachineState.getReg_setPC, MachineState.getReg_setReg_eq,
    MachineState.getReg_setReg_ne]

end CommitGolfCandidate
