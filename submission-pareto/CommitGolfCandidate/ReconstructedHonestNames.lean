import CommitGolfCandidate.ReconstructedHonestWideKernel

namespace CommitGolfCandidate.Reconstruction.HonestNames
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 OracleComp HonestRegionStep HonestProtected HonestRanges HonestMemoryRanges

inductive Atom where | literal | cursor | indices | count | position | leaf
  deriving DecidableEq
structure Term where
  atom : Atom
  offset : Word := 0#64
  deriving DecidableEq
structure Values where
  cursor : Word
  indices : Word
  count : Word
  position : Word

def origin (v : Values) : Atom→Word
  | .literal => 0#64
  | .cursor => v.cursor
  | .indices => v.indices
  | .count => v.count
  | .position => v.position
  | .leaf => (v.position+16777216) >>> 15

def eval (v : Values) (x : Term) := origin v x.atom+x.offset

abbrev RegFile := Reg→Option Term
abbrev MemFile := Word→Option Term
structure Names where
  regs : RegFile
  mem : MemFile

def Means (v : Values) (s : MachineState) (b : Names) :=
  (∀ r x, b.regs r=some x → s.getReg r=eval v x) ∧ (∀ q x, b.mem q=some x → s.getMem q=eval v x)

def value (a : Abstract) (b : Names) (r : Reg) : Option Term :=
  (b.regs r).orElse (fun _ => (singleton (a.regs r)).map (fun k => ⟨.literal,k⟩))

theorem value_ok {a : Abstract} {b : Names} {v : Values} {s : MachineState} (numeric : Models s a)
    (symbolic : Means v s b) {r : Reg} {x : Term} (known : value a b r=some x) : s.getReg r=eval v x := by
  cases h : b.regs r with
  | some t => simp only [value,h,Option.orElse_some,Option.some.injEq] at known; exact known ▸ symbolic.1 _ _ h
  | none =>
    cases p : singleton (a.regs r) with
    | none => simp [value,h,p] at known
    | some w =>
      simp only [value,h,Option.orElse_none,p,Option.map_some,Option.some.injEq] at known
      subst x; simpa only [eval,origin,BitVec.zero_add] using singleton_ok (numeric.1 _) p

def add (x y : Term) : Option Term :=
  if x.atom=.literal then some ⟨y.atom,x.offset+y.offset⟩
  else if y.atom=.literal then some ⟨x.atom,x.offset+y.offset⟩ else none

private theorem add_ok (v : Values) (x y z : Term) (h : add x y=some z) : eval v x+eval v y=eval v z := by
  unfold add at h
  split at h
  · rename_i first
    obtain rfl := Option.some.inj h
    simp only [eval,first,origin,BitVec.zero_add]; ac_rfl
  · split at h
    · rename_i second
      obtain rfl := Option.some.inj h
      simp only [eval,second,origin,BitVec.zero_add]; ac_rfl
    · cases h

private def rhs (a : Abstract) (b : Names) : Instruction→Option Term
  | .base (.ADDI _ reg off) => (value a b reg).bind fun x => add x ⟨.literal,signExtend12 off⟩
  | .base (.ADD _ l r) => (value a b l).bind fun x => (value a b r).bind fun y => add x y
  | .base (.SRLI _ reg amt) =>
    if amt.toNat=15 ∧ value a b reg=some ⟨.position,16777216⟩ then some ⟨.leaf,0#64⟩ else none
  | .base (.LD _ reg off) =>
    if off=0 ∧ value a b reg=some ⟨.indices,0#64⟩ then some ⟨.position,0#64⟩
    else (singleton (addressRange (a.regs reg) off)).bind b.mem
  | _ => none

def nextRegs (a : Abstract) (b : Names) (op : Instruction) (r : Reg) :=
  if r=.x0 then none else if writesReg op r then rhs a b op else b.regs r

private theorem ordinary_regs {v : Values} {s t : MachineState} {a : Abstract} {b : Names} (op : Instruction)
    (numeric : Models s a) (symbolic : Means v s b) (index : s.getMem v.indices=v.position)
    (step : ordinaryStep s op=some t) (r : Reg) (x : Term) (h : nextRegs a b op r=some x) : t.getReg r=eval v x := by
  unfold nextRegs at h; split at h
  · cases h
  · rename_i nz; split at h
    · rename_i written
      cases op with
      | word _ _ _ _ | sraiw _ _ _ => cases h
      | base op =>
        cases op <;> try cases h
        case ADD d l reg =>
          have eq : d=r := by simpa only [writesReg,beq_iff_eq] using written
          subst d
          simp only [rhs,Option.bind_eq_some_iff] at h
          obtain ⟨left,hl,right,hr,term⟩ := h
          simp only [ordinaryStep,memoryArgumentsValid,memAccess,ite_true,Option.some.injEq] at step
          subst t
          simp only [execInstrBr,MachineState.getReg_setPC,MachineState.getReg_setReg_eq nz,
            value_ok numeric symbolic hl,value_ok numeric symbolic hr,add_ok v _ _ _ term]
        case ADDI d reg off =>
          have eq : d=r := by simpa only [writesReg,beq_iff_eq] using written
          subst d
          simp only [rhs,Option.bind_eq_some_iff] at h
          obtain ⟨left,hl,term⟩ := h
          simp only [ordinaryStep,memoryArgumentsValid,memAccess,ite_true,Option.some.injEq] at step
          subst t
          simp only [execInstrBr,MachineState.getReg_setPC,MachineState.getReg_setReg_eq nz,value_ok numeric symbolic hl]
          simpa only [eval,origin,BitVec.zero_add] using add_ok v _ _ _ term
        case SRLI d reg amt =>
          have eq : d=r := by simpa only [writesReg,beq_iff_eq] using written
          subst d
          simp only [rhs,Option.ite_none_right_eq_some,Option.some.injEq] at h
          obtain ⟨⟨shift,tagged⟩,rfl⟩ := h
          simp only [ordinaryStep,memoryArgumentsValid,memAccess,ite_true,Option.some.injEq] at step; subst t
          simp only [execInstrBr,MachineState.getReg_setPC,MachineState.getReg_setReg_eq nz,shift,
            value_ok numeric symbolic tagged,eval,origin,BitVec.add_zero]
        case LD d reg off =>
          have eq : d=r := by simpa only [writesReg,beq_iff_eq] using written
          subst d
          simp only [ordinaryStep,Option.ite_none_right_eq_some,Option.some.injEq] at step
          rw [←step.2]; simp only [execInstrBr,MachineState.getReg_setPC,MachineState.getReg_setReg_eq nz]
          simp only [rhs] at h; split at h
          · rename_i inp
            obtain ⟨rfl,tagged⟩ := inp
            obtain rfl := Option.some.inj h
            rw [value_ok numeric symbolic tagged]
            simp only [eval,origin,show signExtend12 0=0#64 from rfl,BitVec.add_zero,index]
          · simp only [Option.bind_eq_some_iff] at h
            obtain ⟨q,p,cell⟩ := h
            rw [singleton_ok (address_ok (numeric.1 _) off) p]
            exact symbolic.2 _ _ cell
    · rename_i kept
      rw [ordinary_step_keeps _ _ _ _ step (Bool.eq_false_iff.mpr kept)]
      exact symbolic.1 _ _ h

def nextMem (a : Abstract) (b : Names) (op : Instruction) (q : Word) : Option Term :=
  match store op with
  | some w => if w.whole && singleton (addressRange (a.regs w.base) w.offset)==some q then value a b w.source
      else if (writes a op).all (fun win => away win q) then b.mem q else none
  | none => if (writes a op).all (fun win => away win q) then b.mem q else none

def next (a : Abstract) (b : Names) (op : Instruction) : Names := ⟨nextRegs a b op,nextMem a b op⟩

theorem step {v : Values} {s : MachineState} {a : Abstract} {b : Names} (op : Instruction) (coins : Bool)
    (numeric : Models s a) (symbolic : Means v s b) (index : s.getMem v.indices=v.position)
    (read : fetch HonestWideKernel.image s=some op) (pub : op=.base .ECALL → s.getReg .x5=0)
    (out : Execution) (run : out∈support (execute HonestWideKernel.image 1 s coins)) (alive : out.exit=.unfinished) :
    Means v out.state (next a b op) := by
  constructor
  · intro r x h
    by_cases call : op=.base .ECALL
    · subst op
      change nextRegs a b (.base .ECALL) r=some x at h
      simp only [nextRegs,writesReg,Bool.false_eq_true,ite_false] at h
      split at h
      · cases h
      · have old := symbolic.1 _ _ h
        let a' : Abstract := ⟨fun r => point (s.getReg r),fun q => point (s.getMem q)⟩
        obtain ⟨_,agree⟩ := query _ s coins a' ⟨fun _ => precise _,fun _ => precise _⟩ read (pub rfl) out run alive
        have eq := agree.1 r
        exact (BitVec.eq_of_toNat_eq (Nat.le_antisymm eq.2 eq.1)).trans old
    · exact ordinary_regs op numeric symbolic index (HonestAbstract.continued_step _ s op coins read call out run alive) r x h
  · intro q x h
    change nextMem a b op q=some x at h
    have kept (safe : (writes a op).all (fun w => away w q)=true) (cell : b.mem q=some x) :
        out.state.getMem q=eval v x :=
      (HonestPhysical.unchanged _ s coins a op numeric read pub out run alive q safe).trans (symbolic.2 _ _ cell)
    cases desc : store op with
    | none => simp only [nextMem,desc,Option.ite_none_right_eq_some] at h; exact kept h.1 h.2
    | some w =>
      simp only [nextMem,desc] at h; split at h
      · rename_i stored; simp only [Bool.and_eq_true,beq_iff_eq] at stored
        have call : op≠.base .ECALL := by rintro rfl; cases desc
        have write := full_store desc stored.1 (HonestAbstract.continued_step _ s op coins read call out run alive)
        have atQ := singleton_ok (address_ok (numeric.1 w.base) w.offset) stored.2
        change w.address s=q at atQ
        rw [←atQ]; exact write.trans (value_ok numeric symbolic h)
      · simp only [Option.ite_none_right_eq_some] at h; exact kept h.1 h.2

end CommitGolfCandidate.Reconstruction.HonestNames
