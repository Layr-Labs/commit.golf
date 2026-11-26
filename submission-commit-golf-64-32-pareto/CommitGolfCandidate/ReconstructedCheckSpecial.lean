import CommitGolfCandidate.ReconstructedCheckOrdinary

namespace CommitGolfCandidate.Reconstruction.CheckSpecial
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding Binding.Machine CheckValues CheckOrdinary CheckRecorded
set_option maxHeartbeats 900000

inductive Op where
  | basic (op : CheckOrdinary.Op)
  | andi (rd rs : Reg) (off : BitVec 12)
  | subPtr (rd a b : Reg)
  | bnePtr (a b : Reg) (off : BitVec 13)
  deriving Repr

def Op.instr : Op→Instruction
  | .basic op=>op.instr
  | .andi rd rs off=>.base (.ANDI rd rs off)
  | .subPtr rd a b=>.base (.SUB rd a b)
  | .bnePtr a b off=>.base (.BNE a b off)

def pointer : Term→Option Loc | .ptr a=>some a | _=>none

def step (tab : Tables) (m : State) : Op→Option State
  | .basic op=>CheckOrdinary.step tab m op
  | .andi rd rs off=>some {m.set rd (applyOp .bitAnd (m.get rs) (.lit (signExtend12 off))) with pc:=m.pc+4}
  | .subPtr rd a b=>do
    let p ← pointer (m.get a)
    let i ← literal (m.get b)
    return {m.set rd (.ptr {p with offset:=p.offset-i}) with pc:=m.pc+4}
  | .bnePtr a b off=>do
    let l ← pointer (m.get a)
    let r ← pointer (m.get b)
    guard (l.region=r.region)
    return {m with pc:=if l.offset=r.offset then m.pc+4 else m.pc+signExtend13 off}

private theorem ptr_value (env : Env) {t : Term} {p : Loc} (h : pointer t=some p) :
    t.val env=physical env p := by cases t <;> simp_all [pointer,Term.val]

private theorem lit_value (env : Env) {t : Term} {w : Word} (h : literal t=some w) :
    t.val env=w := by cases t <;> simp_all [literal,Term.val]

theorem sound (o : Oracle) (env : Env) (tab : Tables) (layout : Layout env tab)
    (m n : State) (s : MachineState) (h : Matches env m s) (safe : Safe tab m.writes)
    (op : Op) (found : fetch image s=some op.instr) (next : step tab m op=some n) :
    ∃ t, Segment o 1 s t [] ∧ Matches env n t ∧ Safe tab n.writes := by
  cases op with
  | basic op=>exact CheckOrdinary.sound o env tab layout m n s h safe op found next
  | andi rd rs off=>
    simp only [step,Option.some.injEq] at next;subst n
    have run : ordinaryStep s (Op.andi rd rs off).instr=some ((s.setReg rd
        ((applyOp .bitAnd (m.get rs) (.lit (signExtend12 off))).val env)).setPC (m.pc+4)) := by
      rw [op_sound,←h.regs,←h.pc];rfl
    exact ⟨_,plain o _ _ _ found run,set_value env m s h _ _ _,safe⟩
  | subPtr rd a b=>
    cases ap : pointer (m.get a) with
    | none=>simp [step,ap] at next
    | some p=>
      cases bp : literal (m.get b) with
      | none=>simp [step,ap,bp] at next
      | some w=>
        simp [step,ap,bp] at next;subst n
        have run : ordinaryStep s (Op.subPtr rd a b).instr=some ((s.setReg rd
            (physical env {p with offset:=p.offset-w})).setPC (m.pc+4)) := by
          change some ((s.setReg rd (s.getReg a-s.getReg b)).setPC (s.pc+4))=_
          rw [h.regs a,h.regs b,ptr_value env ap,lit_value env bp,h.pc]
          simp [physical,BitVec.sub_eq_add_neg,BitVec.add_assoc]
        exact ⟨_,plain o _ _ _ found run,set_value env m s h _ (.ptr _) _,safe⟩
  | bnePtr a b off=>
    cases ap : pointer (m.get a) with
    | none=>simp [step,ap] at next
    | some l=>
      cases bp : pointer (m.get b) with
      | none=>simp [step,ap,bp] at next
      | some r=>
        by_cases region : l.region=r.region
        · simp [step,ap,bp,region] at next;subst n
          have eq : physical env l=physical env r ↔ l.offset=r.offset := by
            simp [physical,region]
          have run : ordinaryStep s (Op.bnePtr a b off).instr=some (s.setPC
              (if l.offset=r.offset then m.pc+4 else m.pc+signExtend13 off)) := by
            simp [Op.instr,ordinaryStep,memoryArgumentsValid,memAccess,execInstrBr,h.regs,ptr_value env ap,
              ptr_value env bp,h.pc,eq]; split <;> rfl
          exact ⟨_,plain o _ _ _ found run,set_pc env m s h _,safe⟩
        · simp [step,ap,bp,region] at next

end CommitGolfCandidate.Reconstruction.CheckSpecial
