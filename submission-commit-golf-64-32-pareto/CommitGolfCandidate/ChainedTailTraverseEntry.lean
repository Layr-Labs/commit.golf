import CommitGolfCandidate.ChainedTailTraverse

/-! Complete traversal entry, including the empty-row branch. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

def tailNoFields (s : MachineState) : Bool := s.getReg .x22 == 0
def tailEntryState (s : MachineState) : MachineState := execInstrBr s (.BEQ .x22 .x0 56)

theorem tail_entry_pc (s : MachineState) :
    (tailEntryState s).pc = if tailNoFields s then s.pc+56 else s.pc+4 := by
  change (if tailNoFields s then s.setPC (s.pc+56) else s.setPC (s.pc+4)).pc = _
  split <;> rfl

theorem tail_entry_register (s : MachineState) (reg : Reg) : (tailEntryState s).getReg reg = s.getReg reg := by
  by_cases empty : tailNoFields s
  · have same : tailEntryState s = s.setPC (s.pc+56) := ite_eq_left empty
    exact (congrArg (fun st : MachineState => st.getReg reg) same).trans MachineState.getReg_setPC
  · have same : tailEntryState s = s.setPC (s.pc+4) := ite_eq_right empty
    exact (congrArg (fun st : MachineState => st.getReg reg) same).trans MachineState.getReg_setPC

theorem tail_entry_memory (s : MachineState) (query : Word) : (tailEntryState s).getMem query = s.getMem query := by
  by_cases empty : tailNoFields s
  · have same : tailEntryState s = s.setPC (s.pc+56) := ite_eq_left empty
    exact (congrArg (fun st : MachineState => st.getMem query) same).trans MachineState.getMem_setPC
  · have same : tailEntryState s = s.setPC (s.pc+4) := ite_eq_right empty
    exact (congrArg (fun st : MachineState => st.getMem query) same).trans MachineState.getMem_setPC

def tailTraverseState (n : Nat) (s : MachineState) : MachineState :=
  tailFinishState (tailFieldsState n (tailEntryState s))
def tailTraverseCycles (n : Nat) (s : MachineState) : Nat :=
  1+(tailFieldsCycles n (tailEntryState s)+tailFinishCycles (tailFieldsState n (tailEntryState s)))

theorem tail_traverse_execution (image : Image) (base : Word) (code : TailTraverseAt image base)
    (n : Nat) (s : MachineState) (pc : s.pc = base)
    (count : tailNoFields s = decide (n=0)) (ready : TailFieldsReady n (tailEntryState s))
    (valid : ¬tailEmpty (tailFieldsState n (tailEntryState s)) →
      accessValid ((tailFieldsState n (tailEntryState s)).getReg .x20) 1 = true)
    (fuel : Nat) (coins : Bool) :
    execute image (tailTraverseCycles n s+fuel) s coins =
      (do let result ← execute image fuel (tailTraverseState n s) coins
          return result.charge (tailTraverseCycles n s) 0) := by
  have fetched : fetch image s = some (.base (.BEQ .x22 .x0 56)) := by
    apply code ⟨0,by decide⟩
    simpa using pc
  have ordinary : ordinaryStep s (.base (.BEQ .x22 .x0 56)) = some (tailEntryState s) := rfl
  have next : (tailEntryState s).pc = if n=0 then base+56 else base+4 := by
    rw [tail_entry_pc,pc,count]
    by_cases empty : n=0 <;> simp [empty]
  rw [show tailTraverseCycles n s+fuel =
    (tailFieldsCycles n (tailEntryState s)+tailFinishCycles (tailFieldsState n (tailEntryState s))+fuel)+1 by
      unfold tailTraverseCycles; omega,
    execute_ordinary_step image _ _ _ _ coins fetched ordinary,
    tail_fields_finish_execution image base code n _ next ready valid]
  simp [tailTraverseState,tailTraverseCycles,Execution.charge,instructionCycles,Nat.add_assoc]

theorem tail_traverse_bound (n : Nat) (s : MachineState) : tailTraverseCycles n s ≤ 13*n+4 := by
  have fields := tail_fields_finish_bound n (tailEntryState s)
  unfold tailTraverseCycles
  omega

theorem tail_traverse_empty (image : Image) (base : Word) (code : TailTraverseAt image base)
    (s : MachineState) (pc : s.pc = base) (count : tailNoFields s = true)
    (bits : s.getReg .x25 = 0) (fuel : Nat) (coins : Bool) :
    execute image (2+fuel) s coins =
      (do let result ← execute image fuel (tailTraverseState 0 s) coins
          return result.charge 2 0) := by
  have empty : tailEmpty (tailFieldsState 0 (tailEntryState s)) = true := by
    rw [tail_fields_state_zero]
    simp [tailEmpty,tail_entry_register,bits]
  have cycles : tailTraverseCycles 0 s = 2 := by
    simp [tailTraverseCycles,tailFieldsCycles,tailFinishCycles,empty]
  rw [←cycles]
  exact tail_traverse_execution image base code 0 s pc (by simpa using count) trivial (by simp [empty]) fuel coins

end CommitGolfCandidate.Chained.Native
