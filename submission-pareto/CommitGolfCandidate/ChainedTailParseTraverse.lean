import CommitGolfCandidate.ChainedTailParseStep

/-! Inverse row traversal with an exact input-end and zero-padding flag. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute

@[irreducible] def tailParsedFieldsState : Nat → MachineState → MachineState
  | 0,s => s
  | n+1,s => tailParsedFieldsState n (tailParseStepState s)

theorem tail_parsed_fields_zero (s : MachineState) : tailParsedFieldsState 0 s=s := by
  simp only [tailParsedFieldsState]

theorem tail_parsed_fields_succ (n : Nat) (s : MachineState) :
    tailParsedFieldsState (n+1) s=tailParsedFieldsState n (tailParseStepState s) := by
  simp only [tailParsedFieldsState]

def tailParsedFieldsCycles : Nat → MachineState → Nat
  | 0,_ => 0
  | n+1,s => tailParseStepCycles s+tailParsedFieldsCycles n (tailParseStepState s)

def TailParsedFieldsReady : Nat → MachineState → Prop
  | 0,_ => True
  | n+1,s =>
    accessValid (s.getReg .x21+1) 1=true ∧
    (tailNeedsByte (tailWidthState s) → accessValid ((tailWidthState s).getReg .x20) 1=true) ∧
    accessValid ((tailParseRead s).getReg .x21) 1=true ∧
    tailMore (tailParseDecreased s)=decide (n≠0) ∧
    TailParsedFieldsReady n (tailParseStepState s)

private theorem next_pc (s : MachineState) (base : Word) (n : Nat) (pc : s.pc=base+4)
    (more : tailMore (tailParseDecreased s)=decide (n≠0)) :
    (tailParseStepState s).pc=if n=0 then base+72 else base+4 := by
  rw [tail_parse_step_pc s base pc,more]
  by_cases empty : n=0 <;> simp [empty]

theorem tail_parsed_fields_end_pc (n : Nat) (s : MachineState) (base : Word)
    (pc : s.pc=if n=0 then base+72 else base+4) (ready : TailParsedFieldsReady n s) :
    (tailParsedFieldsState n s).pc=base+72 := by
  induction n generalizing s with
  | zero => simpa [tail_parsed_fields_zero] using pc
  | succ n ih =>
    rw [tail_parsed_fields_succ]
    obtain ⟨_,_,_,more,rest⟩ := ready
    have start : s.pc=base+4 := by simpa using pc
    exact ih (tailParseStepState s) (next_pc s base n start more) rest

theorem tail_parsed_fields_execution (image : Image) (base : Word) (code : TailParseAt image base)
    (n : Nat) (s : MachineState) (pc : s.pc=if n=0 then base+72 else base+4)
    (ready : TailParsedFieldsReady n s) (fuel : Nat) (coins : Bool) :
    execute image (tailParsedFieldsCycles n s+fuel) s coins =
      (do let result ← execute image fuel (tailParsedFieldsState n s) coins
          return result.charge (tailParsedFieldsCycles n s) 0) := by
  induction n generalizing s with
  | zero => simp [tailParsedFieldsCycles,tail_parsed_fields_zero,Execution.charge]
  | succ n ih =>
    rw [tail_parsed_fields_succ]
    obtain ⟨width,valid,store,more,rest⟩ := ready
    have start : s.pc=base+4 := by simpa using pc
    rw [tailParsedFieldsCycles,Nat.add_assoc,
      tail_parse_step_execution image base code s start width valid store]
    rw [ih (tailParseStepState s) (next_pc s base n start more) rest]
    simp [Execution.charge,Nat.add_assoc]

theorem tail_parsed_fields_bound (n : Nat) (s : MachineState) : tailParsedFieldsCycles n s≤17*n := by
  induction n generalizing s with
  | zero => simp [tailParsedFieldsCycles]
  | succ n ih =>
    have rest := ih (tailParseStepState s)
    have step := tail_parse_step_bound s
    rw [tailParsedFieldsCycles]
    omega

theorem tail_parsed_fields_validate_execution (image : Image) (base : Word) (code : TailParseAt image base)
    (n : Nat) (s : MachineState) (pc : s.pc=if n=0 then base+72 else base+4)
    (ready : TailParsedFieldsReady n s) (fuel : Nat) (coins : Bool) :
    execute image (tailParsedFieldsCycles n s+3+fuel) s coins =
      (do let result ← execute image fuel (tailValidatePrefix (tailParsedFieldsState n s) 3) coins
          return result.charge (tailParsedFieldsCycles n s+3) 0) := by
  rw [Nat.add_assoc,tail_parsed_fields_execution image base code n s pc ready,
    tail_validate_execution image (base+72) code.validate _ (tail_parsed_fields_end_pc n s base pc ready)]
  simp [Execution.charge,Nat.add_assoc]

theorem tail_parsed_fields_validate_pc (n : Nat) (s : MachineState) (base : Word)
    (pc : s.pc=if n=0 then base+72 else base+4) (ready : TailParsedFieldsReady n s) :
    (tailValidatePrefix (tailParsedFieldsState n s) 3).pc=base+84 := by
  rw [tail_validate_pc _ 3 (by decide),tail_parsed_fields_end_pc n s base pc ready,BitVec.add_assoc]
  rfl

end CommitGolfCandidate.Chained.Native
