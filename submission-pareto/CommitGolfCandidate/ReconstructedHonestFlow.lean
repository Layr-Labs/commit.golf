import CommitGolfCandidate.Execution

namespace CommitGolfCandidate.Reconstruction.HonestFlow
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-- Static successors of one machine instruction, measured in byte addresses.
Indirect returns have to be handled by their caller's return-address invariant. -/
def targets (pc : Word) : Instruction → List Word
  | .base (.BEQ _ _ d) | .base (.BNE _ _ d) | .base (.BLT _ _ d) |
    .base (.BGE _ _ d) | .base (.BLTU _ _ d) | .base (.BGEU _ _ d) => [pc+4,pc+signExtend13 d]
  | .base (.JAL _ d) => [pc+signExtend21 d]
  | .base (.JALR ..) => []
  | _ => [pc+4]

def direct : Instruction → Bool
  | .base (.JALR ..) => false
  | _ => true

def price : Instruction → Nat
  | .base .ECALL => 8
  | i => instructionCycles i

private theorem next_pc (s t : MachineState) (op : Instruction) (ok : direct op = true)
    (step : ordinaryStep s op = some t) : t.pc ∈ targets s.pc op := by
  cases op with
  | word op rd a b => simp only [ordinaryStep,Option.some.injEq] at step; subst t; exact List.mem_cons_self
  | sraiw rd rs n => simp only [ordinaryStep,Option.some.injEq] at step; subst t; exact List.mem_cons_self
  | base i =>
    cases i <;> simp only [direct, Bool.false_eq_true] at ok
    all_goals try contradiction
    all_goals simp only [ordinaryStep] at step
    all_goals try contradiction
    all_goals split at step <;> simp_all only [Option.some.injEq,reduceCtorEq]
    all_goals subst t
    all_goals first | exact List.mem_cons_self | simp only [targets,execInstrBr]; split <;> simp [MachineState.setPC]

private theorem priced (i : Instruction) : 0 < instructionCycles i := by
  cases i with
  | base op => cases op <;> simp [instructionCycles]
  | word op _ _ _ => cases op <;> simp [instructionCycles]
  | sraiw _ _ _ => simp [instructionCycles]

private theorem ordinary_fault (im : Image) (s : MachineState) (op : Instruction) (coins : Bool)
    (read : fetch im s = some op) (fault : ordinaryStep s op = none) (notCall : op ≠ .base .ECALL) :
    execute im 1 s coins = pure ⟨.failure,s,1,0⟩ := by
  cases op with
  | base op => cases op <;> simp_all [execute]
  | word _ _ _ _ | sraiw _ _ _ => simp_all [execute]

private theorem set_zero (s t : MachineState) (step : ordinaryStep s (.base (.ADDI .x5 .x0 0)) = some t) :
    t.getReg .x5 = 0 := by
  simp [ordinaryStep,memoryArgumentsValid,memAccess] at step
  subst t
  rfl

/-- One real interpreter step respects the decoded control-flow graph and price.
The zero assignment immediately before an oracle call is carried into its guard. -/
theorem charged_successors (im : Image) (s : MachineState) (op : Instruction) (coins : Bool)
    (read : fetch im s = some op) (ok : direct op = true)
    (pub : op = .base .ECALL → s.getReg .x5 = 0) (r : Execution) (hr : r ∈ support (execute im 1 s coins)) :
    r.cycles ≤ price op ∧ (r.exit = .unfinished →
      r.state.pc ∈ targets s.pc op ∧ (op = .base (.ADDI .x5 .x0 0) → r.state.getReg .x5 = 0)) := by
  by_cases sys : op = .base .ECALL
  · subst op
    rw [execute,read] at hr
    simp only [pub rfl,ite_true] at hr
    cases input : oracleInput s with
    | none =>
      simp only [input,support_pure,Set.mem_singleton_iff] at hr
      subst r; exact ⟨by change 1 ≤ 8; decide,by intro h; cases h⟩
    | some q =>
      simp only [input,mem_support_bind_iff] at hr
      obtain ⟨answer,_,hr⟩ := hr
      simp only [execute,pure_bind,support_pure,Set.mem_singleton_iff] at hr
      obtain ⟨_,rfl,rfl⟩ := hr
      rcases q with x | (y|z) <;> exact ⟨by change 8 ≤ 8; decide,fun _ => ⟨List.mem_cons_self,by intro h; cases h⟩⟩
  · have fee : price op = instructionCycles op := by
      cases op with
      | base i => cases i <;> simp_all [price]
      | word _ _ _ _ | sraiw _ _ _ => rfl
    cases step : ordinaryStep s op with
    | none =>
      rw [ordinary_fault im s op coins read step sys,support_pure,Set.mem_singleton_iff] at hr
      subst r; exact ⟨fee.symm ▸ priced op,by intro h; cases h⟩
    | some t =>
      rw [execute_ordinary_step im op s t 0 coins read step] at hr
      simp only [execute,pure_bind,support_pure,Set.mem_singleton_iff] at hr
      subst r
      refine ⟨by simp [Execution.charge,fee],fun _ => ⟨next_pc s t op ok step,?_⟩⟩
      rintro rfl; exact set_zero s t step

/-- Facts checked for each vertex. Edges to the next loop entry or its exit
carry no remaining intra-block cost. Other edges must decrease the rank by at
least the fetched instruction price. -/
structure Ranking (im : Image) (active cut zero : Word → Bool) (rank : Word → Nat) : Prop where
  step : ∀ s : MachineState, active s.pc = true → ∃ op,
    fetch im s = some op ∧ direct op = true ∧ (op = .base .ECALL → zero s.pc = true) ∧
    price op ≤ rank s.pc ∧ ∀ pc ∈ targets s.pc op, cut pc = true ∨
      (active pc = true ∧ rank pc + price op ≤ rank s.pc ∧
        (zero pc = true → op = .base (.ADDI .x5 .x0 0)))

/-- A bound on the actual VM for all oracle and coin outcomes, under an
arbitrary continuation bound for the next loop cutpoint. -/
theorem bounded (im : Image) (active cut zero : Word → Bool) (rank : Word → Nat)
    (cert : Ranking im active cut zero rank) (coins : Bool) (tail : Nat)
    (boundary : ∀ t : MachineState, cut t.pc = true → ∀ f r, r ∈ support (execute im f t coins) → r.cycles ≤ tail)
    (s : MachineState) (entry : active s.pc = true) (safe : zero s.pc = true → s.getReg .x5 = 0)
    (f : Nat) (r : Execution) (hr : r ∈ support (execute im f s coins)) : r.cycles ≤ rank s.pc + tail := by
  induction f generalizing s r with
  | zero =>
    simp only [execute,support_pure,Set.mem_singleton_iff] at hr
    subst r; exact Nat.zero_le _
  | succ f ih =>
    obtain ⟨op,read,ok,pub,fee,edges⟩ := cert.step s entry
    rw [show f+1=1+f by omega,execute_add,mem_support_bind_iff] at hr
    obtain ⟨mid,one,rest⟩ := hr
    obtain ⟨charged,post⟩ := charged_successors im s op coins read ok (safe ∘ pub) mid one
    by_cases cont : mid.exit = .unfinished
    · simp only [resume,cont,ite_true,mem_support_bind_iff,support_pure,Set.mem_singleton_iff] at rest
      obtain ⟨out,run,rfl⟩ := rest
      obtain ⟨target,clear⟩ := post cont
      rcases edges _ target with done | ⟨inside,less,zeroNext⟩
      · have b := boundary mid.state done f out run
        change mid.cycles+out.cycles ≤ _
        omega
      · have b := ih mid.state inside (clear ∘ zeroNext) out run
        change mid.cycles+out.cycles ≤ _
        omega
    · simp only [resume,cont,ite_false,support_pure,Set.mem_singleton_iff] at rest
      subst r; omega

end CommitGolfCandidate.Reconstruction.HonestFlow
