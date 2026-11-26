import CommitGolfCandidate.TruncFlow
namespace CommitGolfCandidate.Trunc
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 18000
set_option maxHeartbeats 1500000

def parentStartInstructions : List Instr :=
  [.ADDI .x21 .x23 2560, .ADDI .x24 .x0 1536, .ADDI .x24 .x24 1536,
   .ADDI .x6 .x0 0, .SLLI .x6 .x6 11, .ADDI .x6 .x6 191, .SLLI .x6 .x6 11,
   .ADDI .x6 .x6 2047, .SLLI .x6 .x6 11, .ADDI .x6 .x6 512, .ADD .x22 .x9 .x6]

def parentStartPrefix (state : MachineState) (count : Nat) : MachineState :=
  (parentStartInstructions.take count).foldl execInstrBr state

theorem prepare11 (s : MachineState) (pc : s.pc=6420) :
    Runs (submission.image .commit) s (parentStartPrefix s 11) 11 11 := by
  intro fuel coin
  apply execute_unit_steps (states := parentStartPrefix s)
  intro i hi
  refine ⟨.base ((parentStartInstructions[i]?).getD .EBREAK), ?_, ?_, ?_⟩
  · apply prefixFetch _ (581 + i) _ (by omega)
    · interval_cases i <;>
          simp [parentStartPrefix, parentStartInstructions, execInstrBr, pc, MachineState.setPC]
    · have hf := commit_filtered_parentSetup i (by omega)
      interval_cases i <;> (rw [commit_code_word_at _ _ hf]; rfl)
  · interval_cases i <;> rfl
  · interval_cases i <;> rfl

end CommitGolfCandidate.Trunc
