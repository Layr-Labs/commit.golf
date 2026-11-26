import CommitGolfCandidate.ReconstructedHonestFlow
import CommitGolfCandidate.RegisterPreservation

namespace CommitGolfCandidate.Reconstruction.HonestRegisters
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp HonestFlow

/-- Each tracked register is either a concrete RV64 word or unconstrained. -/
abbrev Known := Reg → Option Word
def Agrees (s : MachineState) (known : Known) := ∀ r v, known r = some v → s.getReg r = v

inductive Expression where
  | constant (value : Word)
  | unary (arg : Reg) (f : Word → Word)
  | binary (left right : Reg) (f : Word → Word → Word)

def Expression.value (s : MachineState) : Expression → Word
  | .constant c => c
  | .unary r f => f (s.getReg r)
  | .binary r t f => f (s.getReg r) (s.getReg t)

def Expression.known (m : Known) : Expression → Option Word
  | .constant c => some c
  | .unary r f => f <$> m r
  | .binary r t f => do return f (←m r) (←m t)

private theorem evaluate (s : MachineState) (m : Known) (agree : Agrees s m) (e : Expression) (v : Word)
    (evaluated : e.known m = some v) : e.value s = v := by
  cases e with
  | constant c => exact Option.some.inj evaluated
  | unary r f =>
    cases read : m r with
    | none => simp [Expression.known,read] at evaluated
    | some x => simpa [Expression.known,Expression.value,read,agree r x read] using evaluated
  | binary r t f =>
    cases read : m r with
    | none => simp [Expression.known,read] at evaluated
    | some x =>
      cases read' : m t with
      | none => simp [Expression.known,read,read'] at evaluated
      | some y => simpa [Expression.known,Expression.value,read,read',agree r x read,agree t y read'] using evaluated

/-- Only operators needed for the cap control registers are concretized. All
other destination values are dropped. The generic register frame preserves
known source values through stores, branches, and unrelated arithmetic. -/
def effect : Instruction → Option (Reg × Expression)
  | .base (.ADD rd a b) => some (rd,.binary a b (·+·))
  | .base (.SUB rd a b) => some (rd,.binary a b (·-·))
  | .base (.AND rd a b) => some (rd,.binary a b (·&&&·))
  | .base (.OR rd a b) => some (rd,.binary a b (·|||·))
  | .base (.ADDI rd a n) => some (rd,.unary a (·+signExtend12 n))
  | .base (.ANDI rd a n) => some (rd,.unary a (·&&&signExtend12 n))
  | .base (.SLLI rd a n) => some (rd,.unary a (·<<<n.toNat))
  | .base (.SRLI rd a n) => some (rd,.unary a (·>>>n.toNat))
  | .base (.LUI rd n) => some (rd,.constant (((n.zeroExtend 32) <<< 12).signExtend 64))
  | .base (.SRLIW rd a n) => some (rd,.unary a (fun x => ((x.truncate 32) >>> n.toNat).signExtend 64))
  | .base (.ADDIW rd a n) => some (rd,.unary a (fun x => (x.truncate 32 + (signExtend12 n).truncate 32).signExtend 64))
  | .word op rd a b => some (rd,.binary a b (fun x y => (wordResult op (x.truncate 32) (y.truncate 32)).signExtend 64))
  | _ => none

private theorem effect_valid (s t : MachineState) (op : Instruction) (step : ordinaryStep s op = some t)
    (rd : Reg) (e : Expression) (description : effect op = some (rd,e)) (nz : rd ≠ .x0) :
    t.getReg rd = e.value s := by
  cases op with
  | base op =>
    cases op <;> simp only [effect,Option.some.injEq,Prod.mk.injEq,reduceCtorEq] at description
    all_goals obtain ⟨rfl,rfl⟩ := description
    all_goals simp only [ordinaryStep,memoryArgumentsValid,memAccess,ite_true,Option.some.injEq] at step
    all_goals subst t
    all_goals simp only [execInstrBr,MachineState.getReg_setPC,MachineState.getReg_setReg_eq nz,Expression.value]
  | word op rd' a b =>
    simp only [effect,Option.some.injEq,Prod.mk.injEq] at description
    obtain ⟨rfl,rfl⟩ := description
    simp only [ordinaryStep,Option.some.injEq] at step
    subst t
    simp only [MachineState.getReg_setPC,MachineState.getReg_setReg_eq nz,Expression.value]
  | sraiw _ _ _ => cases description

def update (m : Known) (op : Instruction) (r : Reg) : Option Word :=
  if r = .x0 then some 0 else if writesReg op r then do
    let (rd,expr) ← effect op
    guard (rd = r)
    expr.known m
  else m r

/-- Register abstraction is sound for every successful ordinary machine step,
with arbitrary memory. A load is allowed to return every possible word. -/
theorem update_valid (s t : MachineState) (op : Instruction) (m : Known) (agree : Agrees s m)
    (step : ordinaryStep s op = some t) : Agrees t (update m op) := by
  intro r v known
  by_cases z : r = .x0
  · subst r; have eq : (0 : Word) = v := by simpa [update] using known
    exact eq
  · cases write : writesReg op r with
    | false =>
      have old : m r = some v := by simpa [update,z,write] using known
      exact (ordinary_step_keeps s t op r step write).trans (agree _ _ old)
    | true =>
      cases desc : effect op with
      | none => simp [update,z,write,desc] at known
      | some pair =>
        obtain ⟨dest,e⟩ := pair
        by_cases loc : dest = r
        · subst dest
          have value : e.known m = some v := by simpa [update,z,write,desc] using known
          exact (effect_valid s t op step r e desc z).trans (evaluate s m agree e v value)
        · simp [update,z,write,desc,loc] at known

end CommitGolfCandidate.Reconstruction.HonestRegisters
