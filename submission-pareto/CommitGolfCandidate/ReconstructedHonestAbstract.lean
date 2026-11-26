import CommitGolfCandidate.ReconstructedHonestRegisters

namespace CommitGolfCandidate.Reconstruction.HonestAbstract
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp HonestFlow HonestRegisters

/-- A representative is used only to decide branch direction when both actual
source operands are tracked. All unconstrained operands remain nondeterministic. -/
private def representative (pc : Word) (m : Known) : MachineState :=
  {initialMachine with pc := pc, regs := fun r => (m r).getD 0}

private theorem rep_read (s : MachineState) (m : Known) (a : Agrees s m) (r : Reg)
    (known : (m r).isSome = true) : (representative s.pc m).getReg r = s.getReg r := by
  cases read : m r with
  | none => simp [read] at known
  | some x =>
    cases r <;> first | rfl | exact (show (representative s.pc m).getReg _ = x by
      change (m _).getD 0 = _; rw [read]; rfl).trans (a _ x read).symm

private def condition : Instr → Option (Reg × Reg)
  | .BEQ x y _ | .BNE x y _ | .BLT x y _ | .BGE x y _ | .BLTU x y _ | .BGEU x y _ => some (x,y)
  | _ => none

private theorem branch_pc (s u t : MachineState) (i : Instr) (x y : Reg)
    (described : condition i = some (x,y)) (pc : u.pc = s.pc)
    (rx : u.getReg x = s.getReg x) (ry : u.getReg y = s.getReg y)
    (step : ordinaryStep s (.base i) = some t) : t.pc = (execInstrBr u i).pc := by
  cases i <;> simp only [condition,Option.some.injEq,Prod.mk.injEq,reduceCtorEq] at described
  all_goals obtain ⟨rfl,rfl⟩ := described
  all_goals simp only [ordinaryStep,memoryArgumentsValid,memAccess,ite_true,Option.some.injEq] at step
  all_goals subst t
  all_goals simp only [execInstrBr,rx,ry]; split <;> simp [MachineState.setPC,pc]

def destinations (pc : Word) (m : Known) : Instruction → List Word
  | .base i =>
    match condition i with
    | some (x,y) => if (m x).isSome && (m y).isSome then [(execInstrBr (representative pc m) i).pc]
      else targets pc (.base i)
    | none => targets pc (.base i)
  | op => targets pc op

private theorem destinations_sound (s t : MachineState) (m : Known) (op : Instruction) (a : Agrees s m)
    (step : ordinaryStep s op = some t) (loose : t.pc ∈ targets s.pc op) : t.pc ∈ destinations s.pc m op := by
  cases op with
  | word _ _ _ _ | sraiw _ _ _ => exact loose
  | base i =>
    cases c : condition i with
    | none => simpa [destinations,c] using loose
    | some pair =>
      obtain ⟨x,y⟩ := pair
      by_cases both : ((m x).isSome && (m y).isSome) = true
      · simp only [destinations,c,both,ite_true,List.mem_singleton]
        simp only [Bool.and_eq_true] at both
        exact branch_pc s (representative s.pc m) t i x y c rfl (rep_read s m a x both.1) (rep_read s m a y both.2) step
      · simpa [destinations,c,both] using loose

theorem continued_step (image : Image) (s : MachineState) (op : Instruction) (coins : Bool)
    (read : fetch image s = some op) (plain : op ≠ .base .ECALL) (out : Execution)
    (run : out ∈ support (execute image 1 s coins)) (cont : out.exit = .unfinished) :
    ordinaryStep s op = some out.state := by
  cases step : ordinaryStep s op with
  | none =>
    have failed : execute image 1 s coins = pure ⟨.failure,s,1,0⟩ := by
      cases op with
      | base i => cases i <;> simp_all [execute]
      | word _ _ _ _ | sraiw _ _ _ => simp_all [execute]
    rw [failed,support_pure,Set.mem_singleton_iff] at run
    subst out; cases cont
  | some t =>
    rw [execute_ordinary_step image op s t 0 coins read step] at run
    simp only [execute,pure_bind,support_pure,Set.mem_singleton_iff] at run
    subst out; rfl

/-- One real step through a non-syscall instruction refines the abstract
register file and one of its possible control-flow destinations. -/
theorem one (image : Image) (s : MachineState) (op : Instruction) (m : Known) (coins : Bool)
    (read : fetch image s = some op) (plain : op ≠ .base .ECALL) (direct' : direct op = true)
    (agree : Agrees s m) (out : Execution) (run : out ∈ support (execute image 1 s coins)) :
    out.cycles ≤ price op ∧ (out.exit = .unfinished → out.state.pc ∈ destinations s.pc m op ∧
      Agrees out.state (update m op)) := by
  obtain ⟨cost,post⟩ := charged_successors image s op coins read direct' (fun h => (plain h).elim) out run
  refine ⟨cost,?_⟩
  intro continued
  have step := continued_step image s op coins read plain out run continued
  exact ⟨destinations_sound s out.state m op agree step (post continued).1,update_valid s out.state op m agree step⟩

end CommitGolfCandidate.Reconstruction.HonestAbstract
