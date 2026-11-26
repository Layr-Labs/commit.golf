import CommitGolfCandidate.S5BatchLoop
namespace CommitGolfCandidate.S5Machine.Open
open CommitGolf CommitGolf.Riscv RiscvZkvm.Rv64
open Late (Levels SaltTape)
open Writer (widths)
def started (s : MachineState) := execInstrBr s (.ADDI .x22 .x0 128)

theorem batch_start (td : Trapdoor) (ps : Positions) (tree : Levels) (salt : SaltTape) (agree : TrapdoorAgrees td tree salt)
    (batch : ps.card=128) :
    ∃ t,Runs (initial td ps) t 118 118 ∧ BatchRegs t 0 (indices ps).length ∧
      FieldCursor tree t [] ∧ InputRows t (indices ps) [] tree salt := by
  obtain ⟨s,head,pc,regs,table,cap,src,marks⟩:=enter_initial td ps tree salt agree (by omega)
  simp only [batch,decide_true,ite_true] at head pc regs
  let t:=started s
  have run : Runs s t 1 1 := fun fuel=>execute_ordinary_step _ _ _ _ _ _
    (site (p:=.opening) (n:=143) (op:=.ADDI .x22 .x0 128) (by decide) (by rfl) s pc) rfl
  have same : t.mem=s.mem:=rfl
  have keep (q : Reg) (ne : q≠.x22) : t.getReg q=s.getReg q :=
    MachineState.getReg_setPC.trans (MachineState.getReg_setReg_ne _ _ _ _ ne.symm)
  have ep : t.pc=pcAt 144:=by change s.pc+4=_;rw [pc];rfl
  have len : (indices ps).length=128 := by simpa only [indices,Finset.length_sort] using batch
  have rr : BatchRegs t 0 (indices ps).length := by
    rw [len];refine ⟨ep,(keep _ (by decide)).trans table,(keep _ (by decide)).trans regs.indices,rfl,
      (keep _ (by decide)).trans regs.salts,(keep _ (by decide)).trans regs.radix,(keep _ (by decide)).trans regs.start,
      (keep _ (by decide)).trans (regs.marks rfl),(keep _ (by decide)).trans (regs.constants rfl).1⟩
  have ptr:=(keep _ (by decide)).trans regs.dest
  have buf:=(keep _ (by decide)).trans (regs.pending rfl).1
  have n:=(keep _ (by decide)).trans (regs.pending rfl).2
  have c : FieldCursor tree t [] := ⟨ptr,n,(keep _ (by decide)).trans (regs.constants rfl).2,
    fun _=>Writer.prefix_zero t proofBase ptr n buf⟩
  have data : InputRows s (indices ps) [] tree salt:=⟨src,cap,fun j hj=>marks j (by omega)⟩
  exact ⟨t,head.trans run,rr,c,inputs_mem data same⟩

theorem batch_records (td : Trapdoor) (ps : Positions) (tree : Levels) (salt : SaltTape) (agree : TrapdoorAgrees td tree salt)
    (batch : ps.card=128) :
    let xs:=indices ps
    let n:=recordSteps tree salt 0 xs
    ∃ t,Runs (initial td ps) t (118+n) (118+(n+12*128)) ∧ BatchRegs t 128 128 ∧
      FieldCursor tree t (recordFields tree salt xs) ∧ InputRows t xs xs tree salt := by
  let xs:=indices ps
  have len : xs.length=128:=by simpa only [xs,indices,Finset.length_sort] using batch
  obtain ⟨u,first,reg,cur,env⟩:=batch_start td ps tree salt agree batch
  obtain ⟨t,all,last,data,input⟩:=batch_loop u xs [] xs tree salt 0 [] (by rw [len];decide) rfl
    (by rw [len];decide) reg env cur
  rw [len] at all last
  refine ⟨t,first.trans all,last,?_,?_⟩
  · simpa only [List.nil_append] using data
  · simpa only [List.nil_append] using input
end CommitGolfCandidate.S5Machine.Open
