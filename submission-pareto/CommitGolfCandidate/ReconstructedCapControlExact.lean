import CommitGolfCandidate.ReconstructedCapControlForward

namespace CommitGolfCandidate.Reconstruction.CapControlExact
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp HonestRanges HonestProtected HonestRegionStep
open HonestCapStages HonestRegisters
open CommitBlocks (addr)
attribute [local irreducible] ArtifactEncoding.decode
set_option maxRecDepth 20000

def extra : Instruction → Option (Reg×Expression)
  | .base (.SRL d a b) => some (d,.binary a b (fun x y => x >>> (y.toNat%64)))
  | .base (.SLTIU d a imm) => some (d,.unary a (fun x => if x.ult (signExtend12 imm) then 1 else 0))
  | _ => none

private theorem correct (s t : MachineState) (op : Instruction) (reg : Reg) (expr : Expression)
    (found : extra op=some (reg,expr)) (nz : reg≠.x0) (step : ordinaryStep s op=some t) :
    t.getReg reg=expr.value s := by
  cases op with
  | base i =>
    cases i <;> simp only [extra,Option.some.injEq,Prod.mk.injEq,reduceCtorEq] at found
    all_goals obtain ⟨rfl,rfl⟩ := found
    all_goals simp only [ordinaryStep,memoryArgumentsValid,memAccess,ite_true,Option.some.injEq] at step
    all_goals subst t
    all_goals simp only [execInstrBr,MachineState.getReg_setPC,MachineState.getReg_setReg_eq nz,Expression.value]
  | word _ _ _ _ => cases found
  | sraiw _ _ _ => cases found

private theorem eval (s : MachineState) (m : Known) (agree : Agrees s m) (e : Expression) (v : Word)
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

def exactWord (a : Abstract) (op : Instruction) : Option (Reg×Word) := do
  let (rd,e) ← extra op
  let w ← e.known (exactFile a.regs)
  return (rd,w)

def advance (a : Abstract) (op : Instruction) : Abstract :=
  let b := HonestRegionStep.advance a op
  match exactWord a op with
  | none => b
  | some (rd,w) => {b with regs := fun i => if rd=i ∧ i≠.x0 then point w else b.regs i}

theorem advance_ok (s t : MachineState) (a : Abstract) (op : Instruction)
    (before : Models s a) (ordinary : ordinaryStep s op=some t) (old : Models t (HonestRegionStep.advance a op)) :
    Models t (advance a op) := by
  unfold advance
  cases h : exactWord a op with
  | none => exact old
  | some pair =>
    rcases pair with ⟨rd,v⟩
    have data : ∃ ex, extra op=some (rd,ex) ∧ ex.known (exactFile a.regs)=some v := by
      unfold exactWord at h
      cases found : extra op with
      | none => simp [found] at h
      | some pair =>
        rcases pair with ⟨r,ex⟩
        cases k : ex.known (exactFile a.regs) with
        | none => simp [found,k] at h
        | some z =>
          simp [found,k] at h
          obtain ⟨rfl,rfl⟩ := h
          exact ⟨ex,rfl,k⟩
    obtain ⟨ex,desc,number⟩ := data
    refine ⟨fun r => ?_,old.2⟩
    change Contains (if rd=r ∧ r≠.x0 then point v else _) _
    split
    · rename_i eq;obtain ⟨rfl,nz⟩ := eq
      rw [correct s t op _ ex desc nz ordinary,eval s _ (exactFile_ok before.1) ex v number];exact precise _
    · exact old.1 r

def check (out : Word→Shape) : Nat→Word→Abstract→Bool
  | 0,_,_ => false
  | n+1,pc,a => match HonestBlocks.readOp Artifact.openingCode pc with
    | none => false
    | some op => HonestBlocks.plain op && HonestFlow.direct op &&
      (HonestAbstract.destinations pc (exactFile a.regs) op).all (fun target =>
        let b := advance a op
        if stops target then fits b (out target) else check out n target b)

theorem sound (out : Word→Shape) (n : Nat) (pc : Word) (a : Abstract)
    (proof : check out n pc a=true) (s t : MachineState) (coin : Bool) (loc : s.pc=pc)
    (before : Models s a) (path : HonestCapState.Path coin s t) : RegFacts.hold t (out t.pc).regs := by
  induction n generalizing s pc a with
  | zero => cases proof
  | succ n ih =>
    cases atCode : HonestBlocks.readOp Artifact.openingCode pc with
    | none => simp [check,atCode] at proof
    | some op =>
      simp only [check,atCode,Bool.and_eq_true] at proof
      obtain ⟨⟨plain,direction⟩,edges⟩ := proof
      have reg : op≠.base .ECALL := by rintro rfl;cases plain
      have get := HonestBlocks.fetch_op Artifact.openingCode HonestCapState.image (Eq.refl (ArtifactEncoding.decode 32 _)) (by decide)
        s op (loc ▸ atCode)
      have move (v : Execution) (run : v∈support (execute HonestCapState.image 1 s coin)) (pos : v.exit=.unfinished) :
          v.state.pc ∈ HonestAbstract.destinations pc (exactFile a.regs) op ∧ Models v.state (advance a op) := by
        have one := HonestRegionStep.one HonestCapState.image s coin a op before get direction (fun eq => (reg eq).elim) v run pos
        exact ⟨loc ▸ one.1,advance_ok s _ a op before (HonestAbstract.continued_step _ s op coin get reg v run pos) one.2⟩
      cases path with
      | hit run cont stop =>
        obtain ⟨target,model⟩ := move _ run cont
        have good := List.all_eq_true.mp edges _ target
        simp only [stop,ite_true] at good
        exact (fits_ok model good).1
      | more run cont inside tail =>
        obtain ⟨target,model⟩ := move _ run cont
        have good := List.all_eq_true.mp edges _ target
        simp only [inside,Bool.false_eq_true,ite_false] at good
        exact ih _ _ good _ rfl model tail

end CommitGolfCandidate.Reconstruction.CapControlExact
