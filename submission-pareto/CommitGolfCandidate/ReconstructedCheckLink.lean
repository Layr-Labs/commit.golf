import CommitGolfCandidate.ReconstructedCheckProgram

namespace CommitGolfCandidate.Reconstruction.CheckLink
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64 Binding Binding.Machine CheckValues CheckOrdinary CheckRecorded
set_option maxHeartbeats 900000

inductive Op where
  | plain (a : CheckSpecial.Op)
  | xori (rd rs : Reg) (imm : BitVec 12)
  | auipc (rd : Reg) (imm : BitVec 20)
  | jalr (rd rs : Reg) (imm : BitVec 12)
  deriving Repr

def Op.instr : Op→Instruction
  | .plain a=>a.instr
  | .xori rd rs i=>.base (.XORI rd rs i)
  | .auipc rd i=>.base (.AUIPC rd i)
  | .jalr rd rs i=>.base (.JALR rd rs i)

def step (tab : Tables) (m : State) : Op→Option State
  | .plain a=>CheckSpecial.step tab m a
  | .xori rd rs off=>some {m.set rd (applyOp .bitXor (m.get rs) (.lit (signExtend12 off))) with pc:=m.pc+4}
  | .auipc rd off=>some {m.set rd (.lit (m.pc+(((off.zeroExtend 32) <<< 12).signExtend 64))) with pc:=m.pc+4}
  | .jalr rd rs off=>do
    let base←literal (m.get rs)
    return {m.set rd (.lit (m.pc+4)) with pc:=(base+signExtend12 off) &&& ~~~1#64}

theorem sound (o : Oracle) (env : Env) (tab : Tables) (layout : Layout env tab)
    (m n : State) (s : MachineState) (h : Matches env m s) (safe : Safe tab m.writes)
    (op : Op) (found : fetch image s=some op.instr) (next : step tab m op=some n) :
    ∃ t, Segment o 1 s t [] ∧ Matches env n t ∧ Safe tab n.writes := by
  cases op with
  | plain a=>exact CheckSpecial.sound o env tab layout m n s h safe a found next
  | xori rd rs off=>
    simp only [step,Option.some.injEq] at next;subst n
    have run : ordinaryStep s (Op.xori rd rs off).instr=some ((s.setReg rd
      ((applyOp .bitXor (m.get rs) (.lit (signExtend12 off))).val env)).setPC (m.pc+4)) := by
      rw [op_sound,←h.regs,←h.pc];rfl
    exact ⟨_,plain o _ _ _ found run,set_value env m s h _ _ _,safe⟩
  | auipc rd off=>
    simp only [step,Option.some.injEq] at next;subst n
    have run : ordinaryStep s (Op.auipc rd off).instr=some ((s.setReg rd
      (m.pc+(((off.zeroExtend 32) <<< 12).signExtend 64))).setPC (m.pc+4)) := by rw [←h.pc];rfl
    exact ⟨_,plain o _ _ _ found run,set_value env m s h _ (.lit _) _,safe⟩
  | jalr rd rs off=>
    cases src : literal (m.get rs) with
    | none=>simp [step,src] at next
    | some base=>
      simp [step,src] at next;subst n
      have value (x : Term) (eq : literal x=some base) : x.val env=base := by cases x <;> simp_all [literal,Term.val]
      have run : ordinaryStep s (Op.jalr rd rs off).instr=some ((s.setReg rd (m.pc+4)).setPC
          ((base+signExtend12 off) &&& ~~~1#64)) := by rw [←value _ src,←h.regs,←h.pc];rfl
      exact ⟨_,plain o _ _ _ found run,set_value env m s h _ (.lit _) _,safe⟩

def run (tab : Tables) (pc : Word) : List Op→State→Option State
  | [],m=>some m
  | op::ops,m=>if m.pc=pc then do
    let v←step tab m op
    run tab (pc+4) ops v
  else none

def Decoded : List Op→Word→Prop
  | [],_=>True
  | op::xs,pc=>(∀ s : MachineState,s.pc=pc→fetch image s=some op.instr) ∧ Decoded xs (pc+4)

theorem run_sound (o : Oracle) (env : Env) (tab : Tables) (layout : Layout env tab)
    (ops : List Op) (pc : Word) (m last : State) (s : MachineState) (h : Matches env m s) (safe : Safe tab m.writes)
    (fetches : Decoded ops pc) (checked : run tab pc ops m=some last) :
    ∃ t, Segment o ops.length s t [] ∧ Matches env last t ∧ Safe tab last.writes := by
  induction ops generalizing m s pc with
  | nil=>cases checked;exact ⟨s,empty o s,h,safe⟩
  | cons op rest ih=>
    by_cases addr : m.pc=pc
    · cases next : step tab m op with
      | none=>simp [run,addr,next] at checked
      | some v=>
        simp [run,addr,next] at checked
        obtain ⟨u,one,hu,valid⟩:=sound o env tab layout m v s h safe op (fetches.1 _ (h.pc.trans addr)) next
        obtain ⟨t,more,ht,vt⟩:=ih (pc+4) v u hu valid fetches.2 checked
        exact ⟨t,by simpa [Nat.add_comm] using compose one more,ht,vt⟩
    · simp [run,addr] at checked

end CommitGolfCandidate.Reconstruction.CheckLink
