import CommitGolfCandidate.ChainedTailParseTraverse

/-! Complete inverse-row execution, including the empty path and final flag. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

def tailParseEntryState (s : MachineState) : MachineState := execInstrBr s (.BEQ .x22 .x0 72)

theorem tail_parse_entry_pc (s : MachineState) :
    (tailParseEntryState s).pc=if tailNoFields s then s.pc+72 else s.pc+4 := by
  change (if tailNoFields s then s.setPC (s.pc+72) else s.setPC (s.pc+4)).pc = _
  split <;> rfl

theorem tail_parse_entry_register (s : MachineState) (reg : Reg) :
    (tailParseEntryState s).getReg reg=s.getReg reg := by
  by_cases empty : tailNoFields s
  · have same : tailParseEntryState s=s.setPC (s.pc+72) := ite_eq_left empty
    exact (congrArg (fun st : MachineState => st.getReg reg) same).trans MachineState.getReg_setPC
  · have same : tailParseEntryState s=s.setPC (s.pc+4) := ite_eq_right empty
    exact (congrArg (fun st : MachineState => st.getReg reg) same).trans MachineState.getReg_setPC

def tailParseTraverseState (n : Nat) (s : MachineState) : MachineState :=
  tailValidatePrefix (tailParsedFieldsState n (tailParseEntryState s)) 3
def tailParseTraverseCycles (n : Nat) (s : MachineState) : Nat :=
  1+(tailParsedFieldsCycles n (tailParseEntryState s)+3)

theorem tail_parse_traverse_execution (image : Image) (base : Word) (code : TailParseAt image base)
    (n : Nat) (s : MachineState) (pc : s.pc=base)
    (count : tailNoFields s=decide (n=0)) (ready : TailParsedFieldsReady n (tailParseEntryState s))
    (fuel : Nat) (coins : Bool) :
    execute image (tailParseTraverseCycles n s+fuel) s coins =
      (do let result ← execute image fuel (tailParseTraverseState n s) coins
          return result.charge (tailParseTraverseCycles n s) 0) := by
  have fetched : fetch image s=some (.base (.BEQ .x22 .x0 72)) := by
    apply code ⟨0,by decide⟩
    simpa using pc
  have ordinary : ordinaryStep s (.base (.BEQ .x22 .x0 72))=some (tailParseEntryState s) := rfl
  have next : (tailParseEntryState s).pc=if n=0 then base+72 else base+4 := by
    rw [tail_parse_entry_pc,pc,count]
    by_cases empty : n=0 <;> simp [empty]
  rw [show tailParseTraverseCycles n s+fuel =
      (tailParsedFieldsCycles n (tailParseEntryState s)+3+fuel)+1 by unfold tailParseTraverseCycles; omega,
    execute_ordinary_step image _ _ _ _ coins fetched ordinary,
    tail_parsed_fields_validate_execution image base code n _ next ready]
  simp [tailParseTraverseState,tailParseTraverseCycles,Execution.charge,instructionCycles,Nat.add_assoc]

theorem tail_parse_traverse_bound (n : Nat) (s : MachineState) : tailParseTraverseCycles n s≤17*n+4 := by
  have fields := tail_parsed_fields_bound n (tailParseEntryState s)
  unfold tailParseTraverseCycles
  omega

theorem tail_parse_traverse_flag (n : Nat) (s : MachineState) :
    (tailParseTraverseState n s).getReg .x24 =
      if (tailParsedFieldsState n (tailParseEntryState s)).getReg .x20 =
          (tailParsedFieldsState n (tailParseEntryState s)).getReg .x19 ∧
          (tailParsedFieldsState n (tailParseEntryState s)).getReg .x23=0#64 then 1#64 else 0#64 := by
  exact tail_validate_flag _

theorem tail_parse_empty_flag (s : MachineState) :
    (tailParseTraverseState 0 s).getReg .x24 =
      if s.getReg .x20=s.getReg .x19 ∧ s.getReg .x23=0#64 then 1#64 else 0#64 := by
  rw [tail_parse_traverse_flag,tail_parsed_fields_zero]
  simp only [tail_parse_entry_register]

theorem tail_parse_empty_execution (image : Image) (base : Word) (code : TailParseAt image base)
    (s : MachineState) (pc : s.pc=base) (count : tailNoFields s=true) (fuel : Nat) (coins : Bool) :
    execute image (4+fuel) s coins =
      (do let result ← execute image fuel (tailParseTraverseState 0 s) coins
          return result.charge 4 0) := by
  simpa [tailParseTraverseCycles,tailParsedFieldsCycles] using
    tail_parse_traverse_execution image base code 0 s pc (by simpa using count) trivial fuel coins

end CommitGolfCandidate.Chained.Native
