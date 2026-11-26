import CommitGolfCandidate.OpeningWordCopyRun

namespace CommitGolfCandidate.OpeningWordCopy
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxHeartbeats 1100000
attribute [local irreducible] execute

/-- The suffix either copies the last halfword or restores the old x31 value,
then jumps over the unused slots to the original field boundary. -/
def finishInstructions (halfwords : Nat) : List Instr :=
  let words := halfwords/2
  let body := 2*words+(if halfwords%2=0 then 1 else 2)
  let jump := Instr.JAL .x0 (BitVec.ofNat 21 (4*(2*halfwords-body)))
  if halfwords%2=0 then [.SRLI .x31 .x31 16, jump] else
    [.LHU .x31 .x7 (BitVec.ofNat 12 (4*words)),
      .SH .x21 .x31 (BitVec.ofNat 12 (4*words)), jump]

def finishPrefix (halfwords : Nat) (state : MachineState) (count : Nat) :=
  ((finishInstructions halfwords).take count).foldl execInstrBr state

def finishState (halfwords : Nat) (state : MachineState) :=
  finishPrefix halfwords state (finishInstructions halfwords).length

def FieldWidth (halfwords : Nat) : Prop := halfwords=8 ∨ halfwords=15 ∨ halfwords=16

theorem finish_cost (halfwords : Nat) (width : FieldWidth halfwords) :
    2*(halfwords/2)+(finishInstructions halfwords).length=halfwords+2 := by
  rcases width with rfl | rfl | rfl <;> decide

theorem finish_prefix_pc (halfwords : Nat) (width : FieldWidth halfwords) (state : MachineState)
    (count : Nat) (inside : count < (finishInstructions halfwords).length) :
    (finishPrefix halfwords state count).pc=state.pc+BitVec.ofNat 64 (4*count) := by
  rcases width with rfl | rfl | rfl <;>
    norm_num [finishInstructions] at inside <;>
    interval_cases count <;>
    simp [finishPrefix, finishInstructions, execInstrBr, MachineState.setPC, MachineState.setReg, BitVec.add_assoc]

theorem finish_pc (halfwords : Nat) (width : FieldWidth halfwords) (state : MachineState) :
    (finishState halfwords state).pc =
      state.pc+BitVec.ofNat 64 (4*(2*halfwords-2*(halfwords/2))) := by
  rcases width with rfl | rfl | rfl <;>
    simp [finishState,finishPrefix,finishInstructions,execInstrBr,signExtend21,BitVec.add_assoc,
      MachineState.setPC,MachineState.setReg]

theorem finish_register (halfwords : Nat) (width : FieldWidth halfwords) (state : MachineState)
    (reg : Reg) (kept : reg≠.x31) :
    (finishState halfwords state).getReg reg=state.getReg reg := by
  rcases width with rfl | rfl | rfl <;> cases reg <;>
    simp_all [finishState,finishPrefix,finishInstructions,execInstrBr,
      MachineState.getReg,MachineState.setReg,MachineState.setPC,MachineState.setHalfword,MachineState.setMem]

theorem finish_memory (halfwords : Nat) (width : FieldWidth halfwords) (state : MachineState) :
    (finishState halfwords state).mem =
      if halfwords%2=0 then state.mem else
        (state.setHalfword (state.getReg .x21+BitVec.ofNat 64 (4*(halfwords/2)))
          (state.getHalfword (state.getReg .x7+BitVec.ofNat 64 (4*(halfwords/2))))).mem := by
  rcases width with rfl | rfl | rfl <;>
    simp [finishState,finishPrefix,finishInstructions,execInstrBr,signExtend12,
      MachineState.setPC,MachineState.setReg,MachineState.getReg,
      MachineState.setHalfword,MachineState.setMem,MachineState.getMem]

theorem finish_execute (image : Image) (start halfwords : Nat) (width : FieldWidth halfwords)
    (fetched : ∀ i : Fin (finishInstructions halfwords).length, ∀ state : MachineState,
      state.pc=BitVec.ofNat 64 (4096+4*(start+2*(halfwords/2)+i.val)) →
        fetch image state=some (.base ((finishInstructions halfwords)[i.val]?.getD .EBREAK)))
    (state : MachineState)
    (pc : state.pc=BitVec.ofNat 64 (4096+4*(start+2*(halfwords/2))))
    (source : halfwords=15 → accessValid (state.getReg .x7+28) 2=true)
    (target : halfwords=15 → accessValid (state.getReg .x21+28) 2=true)
    (fuel : Nat) (coins : Bool) :
    execute image ((finishInstructions halfwords).length+fuel) state coins = do
      let result ← execute image fuel (finishState halfwords state) coins
      return result.charge (finishInstructions halfwords).length 0 := by
  apply execute_unit_steps (states := finishPrefix halfwords state)
  intro i inside
  refine ⟨.base ((finishInstructions halfwords)[i]?.getD .EBREAK), ?_, ?_, ?_⟩
  · apply fetched ⟨i,inside⟩
    change (finishPrefix halfwords state i).pc=
      BitVec.ofNat 64 (4096+4*(start+2*(halfwords/2)+i))
    rw [finish_prefix_pc halfwords width state i inside,pc,
      ← BitVec.ofNat_add]
    congr 1
    omega
  · rcases width with rfl | rfl | rfl <;>
      norm_num [finishInstructions] at inside <;>
      interval_cases i <;>
      simp [finishPrefix,finishInstructions,ordinaryStep,memoryArgumentsValid,memAccess,
        execInstrBr,signExtend12,
        MachineState.setPC,MachineState.setReg,MachineState.getReg] <;>
      first
      | simpa [MachineState.getReg] using source rfl
      | simpa [MachineState.getReg] using target rfl
  · rcases width with rfl | rfl | rfl <;>
      norm_num [finishInstructions] at inside <;>
      interval_cases i <;> rfl

end CommitGolfCandidate.OpeningWordCopy
