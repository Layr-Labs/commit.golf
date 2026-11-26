import CommitGolfCandidate.S5CapPairHead

namespace CommitGolfCandidate.S5Machine.Check
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Open (W)

structure TrialRegs (H : Compression) (x : CheckInput) (q : Fin 4) (s : MachineState) : Prop where
  addr : s.getReg .x9=W (slotAddr 170)
  baseWord : s.getReg .x18=(slotValue x 0 170).extractLsb' 192 64
  trial : s.getReg .x19=W q.val
  limit : s.getReg .x20=W 4
  left : s.getReg .x21=markedWord (lookup H x 128 340)
  right : s.getReg .x22=markedWord (lookup H x 128 341)

theorem TrialRegs.same {H x q s t} (regs : TrialRegs H x q s) (keep : CapKeeps s t) : TrialRegs H x q t :=
  ⟨(keep _ (by decide)).trans regs.addr,(keep _ (by decide)).trans regs.baseWord,
   (keep _ (by decide)).trans regs.trial,(keep _ (by decide)).trans regs.limit,
   (keep _ (by decide)).trans regs.left,(keep _ (by decide)).trans regs.right⟩

def bothMarked (H : Compression) (x : CheckInput) :=
  (lookup H x 128 340).isSome && (lookup H x 128 341).isSome

private def setupOps : List Sym.Calc := [
  .lui .x9 22,.addi .x9 .x9 1344,.ld .x18 .x9 24,.addi .x19 .x0 1,.addi .x20 .x0 4,
  .lui .x6 16,.addi .x6 .x6 1364,.lbu .x21 .x6 0,.lbu .x22 .x6 1,.band .x6 .x21 .x22]

private theorem both_marks_test (a b : Option Late.Digest) :
    ((markedWord a &&& markedWord b) == 0#64)= !(a.isSome && b.isSome) := by
  cases a <;> cases b <;> simp [markedWord,markBit]

private theorem dispatch_marks (o : Oracle) (s : MachineState) (both : Bool)
    (pc : s.pc=pcAt 1123) (test : Rel.eq.test (s.getReg .x6) (s.getReg .x0)= !both) :
    ∃ t n,n≤2 ∧ Flow o s t n 0 ∧ t.pc=pcAt (if both then 2333 else 1125) ∧ t.mem=s.mem ∧
      ∀ r,t.getReg r=s.getReg r := by
  have br:=branch o s 1123 1125 .eq .x6 .x0 (by decide +kernel) pc _ test
  cases both
  · exact ⟨_,1,by decide,br,rfl,rfl,fun _=>MachineState.getReg_setPC⟩
  · let u:=s.setPC (pcAt 1124)
    have one : Flow o s u 1 0:=br
    have j:=jump o u 1124 2333 .x0 (by decide +kernel) rfl
    exact ⟨_,2,by decide,one.trans j,rfl,rfl,fun r=>MachineState.getReg_setPC.trans
      (show u.getReg r=s.getReg r from MachineState.getReg_setPC)⟩

attribute [local irreducible] readBuffer slotValue lookup

theorem trial_setup (o : Oracle) (x : CheckInput) (s : MachineState) (pc : s.pc=pcAt 1113)
    (ev : Evidence o.compression x 0 s) :
    ∃ t n,n≤12 ∧ Flow o s t n 0 ∧ t.pc=pcAt (if bothMarked o.compression x then 2333 else 1125) ∧
      TrialRegs o.compression x 1 t ∧ t.mem=s.mem ∧ ∀ r∈([.x8,.x25,.x26] : List Reg),t.getReg r=s.getReg r := by
  have access : ∀ a∈Sym.requirements Sym.original setupOps,accessValid (a.1.eval s) a.2=true := by
    intro a ha
    change a∈[(Sym.Expr.lit (W (slotAddr 170+24)),8),(.lit (W (marksBuf+340)),1),(.lit (W (marksBuf+341)),1)] at ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    rcases ha with rfl|rfl|rfl <;> simp only [Sym.Expr.eval] <;> decide
  let u:=Sym.evaluated setupOps s
  obtain ⟨run,regs,mem,ep⟩:=Sym.compiled o setupOps 1113 s pc (by decide +kernel) access
  have orig:=read_digest_word s (slotAddr 170) 3 (by decide) (by decide)
  rw [ev.slot 170 (by decide)] at orig
  have values : TrialRegs o.compression x 1 u :=
    ⟨regs .x9,(regs .x18).trans orig.symm,regs .x19,regs .x20,
      (regs .x21).trans (congrArg (fun b : Byte=>b.zeroExtend 64) (ev.mark 340 (by decide))),
      (regs .x22).trans (congrArg (fun b : Byte=>b.zeroExtend 64) (ev.mark 341 (by decide)))⟩
  have kept (r : Reg) (h : r∈([.x8,.x25,.x26] : List Reg)) : u.getReg r=s.getReg r := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl <;> apply regs
  have flags : u.getReg .x6=u.getReg .x21 &&& u.getReg .x22 := by rw [regs .x6,regs .x21,regs .x22];rfl
  have test : Rel.eq.test (u.getReg .x6) (u.getReg .x0)= !bothMarked o.compression x := by
    change (u.getReg .x6 == 0#64)=_
    rw [flags,values.left,values.right]
    exact both_marks_test _ _
  obtain ⟨t,n,lim,step,ip,tm,tk⟩:=dispatch_marks o u (bothMarked o.compression x) ep test
  have head : Flow o s u 10 0:=run
  exact ⟨t,10+n,by omega,head.trans step,ip,values.same (fun r _=>tk r),
    tm.trans mem,fun r h=>(tk r).trans (kept r h)⟩
end CommitGolfCandidate.S5Machine.Check
