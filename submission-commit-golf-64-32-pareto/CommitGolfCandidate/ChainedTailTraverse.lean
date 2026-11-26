import CommitGolfCandidate.ChainedTailTraverseStep

/-! Native row-count induction and composition with the final partial-byte flush. -/
namespace CommitGolfCandidate.Chained.Native
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp
set_option maxRecDepth 8192
attribute [local irreducible] execute
attribute [local irreducible] tailStepState tailStepDecreased tailStepEmitted

@[irreducible] def tailFieldsState : Nat → MachineState → MachineState
  | 0,s => s
  | n+1,s => tailFieldsState n (tailStepState s)

theorem tail_fields_state_zero (s : MachineState) : tailFieldsState 0 s = s := by
  simp only [tailFieldsState]

theorem tail_fields_state_succ (n : Nat) (s : MachineState) :
    tailFieldsState (n+1) s = tailFieldsState n (tailStepState s) := by
  simp only [tailFieldsState]

def tailFieldsCycles : Nat → MachineState → Nat
  | 0,_ => 0
  | n+1,s => tailStepCycles s+tailFieldsCycles n (tailStepState s)

def TailFieldsReady : Nat → MachineState → Prop
  | 0,_ => True
  | n+1,s =>
    accessValid (s.getReg .x21) 1 = true ∧
    accessValid (s.getReg .x21+1) 1 = true ∧
    (¬tailSkips (tailAppendPrefix (tailLoadPrefix s 3) 3) →
      accessValid ((tailLoadPrefix s 3).getReg .x20) 1 = true) ∧
    tailMore (tailStepDecreased s) = decide (n ≠ 0) ∧
    TailFieldsReady n (tailStepState s)

private theorem next_pc (s : MachineState) (base : Word) (n : Nat) (pc : s.pc = base+4)
    (more : tailMore (tailStepDecreased s) = decide (n ≠ 0)) :
    (tailStepState s).pc = if n=0 then base+56 else base+4 := by
  rw [tail_step_end_pc s base pc,more]
  by_cases empty : n=0 <;> simp [empty]

theorem tail_fields_end_pc (n : Nat) (s : MachineState) (base : Word)
    (pc : s.pc = if n=0 then base+56 else base+4) (ready : TailFieldsReady n s) :
    (tailFieldsState n s).pc = base+56 := by
  induction n generalizing s with
  | zero => simpa [tail_fields_state_zero] using pc
  | succ n ih =>
    rw [tail_fields_state_succ]
    obtain ⟨_,_,_,more,rest⟩ := ready
    have start : s.pc = base+4 := by simpa using pc
    exact ih (tailStepState s) (next_pc s base n start more) rest

theorem tail_fields_execution (image : Image) (base : Word) (code : TailTraverseAt image base)
    (n : Nat) (s : MachineState) (pc : s.pc = if n=0 then base+56 else base+4)
    (ready : TailFieldsReady n s) (fuel : Nat) (coins : Bool) :
    execute image (tailFieldsCycles n s+fuel) s coins =
      (do let result ← execute image fuel (tailFieldsState n s) coins
          return result.charge (tailFieldsCycles n s) 0) := by
  induction n generalizing s with
  | zero => simp [tailFieldsCycles,tail_fields_state_zero,Execution.charge]
  | succ n ih =>
    rw [tail_fields_state_succ]
    obtain ⟨value,width,valid,more,rest⟩ := ready
    have start : s.pc = base+4 := by simpa using pc
    rw [tailFieldsCycles,Nat.add_assoc,
      tail_step_execution image base code s start value width valid]
    rw [ih (tailStepState s) (next_pc s base n start more) rest]
    simp [Execution.charge,Nat.add_assoc]

theorem tail_fields_cycles_bound (n : Nat) (s : MachineState) : tailFieldsCycles n s ≤ 13*n := by
  induction n generalizing s with
  | zero => simp [tailFieldsCycles]
  | succ n ih =>
    have rest := ih (tailStepState s)
    have step := tail_step_cycles_bound s
    rw [tailFieldsCycles]
    omega

theorem tail_fields_finish_execution (image : Image) (base : Word) (code : TailTraverseAt image base)
    (n : Nat) (s : MachineState) (pc : s.pc = if n=0 then base+56 else base+4)
    (ready : TailFieldsReady n s)
    (valid : ¬tailEmpty (tailFieldsState n s) → accessValid ((tailFieldsState n s).getReg .x20) 1 = true)
    (fuel : Nat) (coins : Bool) :
    execute image (tailFieldsCycles n s+tailFinishCycles (tailFieldsState n s)+fuel) s coins =
      (do let result ← execute image fuel (tailFinishState (tailFieldsState n s)) coins
          return result.charge (tailFieldsCycles n s+tailFinishCycles (tailFieldsState n s)) 0) := by
  rw [Nat.add_assoc,tail_fields_execution image base code n s pc ready,
    tail_finish_execution image (base+56) code.finish _ (tail_fields_end_pc n s base pc ready) valid]
  simp [Execution.charge,Nat.add_assoc]

theorem tail_fields_finish_pc (n : Nat) (s : MachineState) (base : Word)
    (pc : s.pc = if n=0 then base+56 else base+4) (ready : TailFieldsReady n s) :
    (tailFinishState (tailFieldsState n s)).pc = base+68 := by
  rw [tail_finish_end_pc,tail_fields_end_pc n s base pc ready,BitVec.add_assoc]
  rfl

theorem tail_fields_finish_bound (n : Nat) (s : MachineState) :
    tailFieldsCycles n s+tailFinishCycles (tailFieldsState n s) ≤ 13*n+3 := by
  have fields := tail_fields_cycles_bound n s
  unfold tailFinishCycles
  split <;> omega

end CommitGolfCandidate.Chained.Native
